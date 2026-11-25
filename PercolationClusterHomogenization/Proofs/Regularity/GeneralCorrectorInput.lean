import PercolationClusterHomogenization.Proofs.Regularity.GeneralAffineApproximationHolds
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneLift
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderOneDimension
import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicDegreeTwo
import PercolationClusterHomogenization.Proofs.Regularity.InfiniteClusterBalls
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# The qualitative corrector input in every dimension

`supercriticalBondCorrectorInput_holds` proves `LatticeProb.External.SupercriticalBondCorrectorInput`
(Armstrong and Dario, arXiv:1609.09431v2, Theorem 2 (i) and (ii) at `k = 1`, in the qualitative form
used by Dario and Gu, Proposition 2.12) in every dimension `d ≥ 2`, with no hypothesis:

* every slope has a corrected plane (`correctedPlaneExistence_holds`);
* two corrected planes of the same slope differ by a constant, by the Liouville theorem of order
  zero (`componentL2Subpolynomial_zero_of_slopeAsymptotics` and `armstrongDarioOrderZero_holds`);
* `dim 𝒜_1 ≤ d + 1` (`orderOneDimension_le`): by (7.18) at `k = 2` in every dimension
  (`armstrongDarioMesoscopicDegreeTwo_holds`), every element of `𝒜_1` is a combination of the
  constants and of the corrected planes of slopes `eᵢ` (`eq_clusterLiftMap_of_orderOne`);
* a function on a cluster whose balls have the cap density determines its slope
  (`eq_zero_of_slopeAsymptotics_zero`), so `(q, a) ↦ u_q + a` is an injective linear map from
  `ℝ^d × ℝ` into `𝒜_1`, hence onto `𝒜_1`, and every element of `𝒜_1` has a unique slope.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Filter MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- A function with slope asymptotics of slope zero has the growth of order zero: its normalized
`L²` norm on the Euclidean ball of radius `R` is `o(R)`. -/
theorem componentL2Subpolynomial_zero_of_slopeAsymptotics {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) (hu : componentSlopeAsymptotics C 0 u) :
    componentL2Subpolynomial C 0 u := by
  rw [componentL2Subpolynomial, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨R₀, fun R hR => ?_⟩
  have hRp : 0 < R := hR₀.trans_le hR
  have hball : componentBallL2 C 0 R u ≤ ε / 2 * R := by
    apply LatticeProb.Percolation.componentBallL2_le_of_abs_le C 0 R u (by positivity)
    intro x hx
    simpa [componentSlope] using htail R hR x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (componentL2_scaled_nonneg C 0 u hRp.le)]
  calc
    (R ^ (0 + 1))⁻¹ * componentBallL2 C 0 R u ≤ (R ^ (0 + 1))⁻¹ * (ε / 2 * R) :=
      mul_le_mul_of_nonneg_left hball (by positivity)
    _ = ε / 2 := by rw [zero_add, pow_one]; field_simp
    _ < ε := half_lt_self hε

/-- **A function determines its slope** on a cluster whose balls have the cap density: if the
zero function has slope asymptotics of slope `v`, then `v = 0`. -/
theorem eq_zero_of_slopeAsymptotics_zero {ω : Configuration d} (C : OpenComponent ω) {X δ : ℝ}
    (hδ : 0 < δ) (hcap : ∀ R : ℝ, ClusterBallCapDensity C 0 X R δ)
    {v : Fin d → ℝ} (h : componentSlopeAsymptotics C v (fun _ => (0 : ℝ))) : v = 0 := by
  set p : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v with hpdef
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

/-- **`dim 𝒜_1 ≤ d + 1` on the infinite cluster of `ℤᵈ`** (Armstrong and Dario, Theorem 2 (i) at
`k = 1`), `d ≥ 2`. -/
theorem orderOneDimension_le [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) ∧
        Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) ≤ d + 1 := by
  obtain ⟨s₁, C₁, δ, -, -, hδ, X, -, -, -, A₀, hae₁⟩ :=
    armstrongDarioMesoscopicDegreeTwo_holds d hd p hpc hp1
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₂, C₂, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1)
    (quadLocality d (capFraction d (theta d p / 2)))
  obtain ⟨M, -, -, -, hae₂⟩ := hcube 0
  filter_upwards [hae₁, hae₂, correctedPlaneExistence_holds hd p hpc hp1] with ω h₁ h₂ h₃
  intro h
  choose g hg using fun i : Fin d => h₃ h (Pi.single i 1)
  have hle : harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ≤
      LinearMap.range (clusterLiftLinear (uniqueInfiniteComponent h) g) := by
    intro u hu
    obtain ⟨ℓ, hℓ⟩ := eq_clusterLiftMap_of_orderOne (uniqueInfiniteComponent h)
      (by positivity : (0 : ℝ) < theta d p / 2) hδ (h₂ h) (h₁ h) hg hu
    exact ⟨ℓ, hℓ.symm⟩
  refine ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans
    ((LinearMap.finrank_range_le _).trans (le_of_eq ?_))⟩
  rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, add_comm]

/-- **The qualitative corrector input in every dimension** (Armstrong and Dario, Theorem 2 (i),
(ii) at `k = 1`; Dario and Gu, Proposition 2.12, qualitative part): almost surely, each slope has a
unique corrected plane normalized at a vertex, and every element of `𝒜_1` has a unique slope. -/
theorem supercriticalBondCorrectorInput_holds :
    LatticeProb.External.SupercriticalBondCorrectorInput := by
  classical
  intro d _ hd p hpc hp1
  obtain ⟨s₀, C₀, K₀, δ, -, -, -, hδ, hcap⟩ := infiniteCluster_ballVolume_capDensity hd p hpc hp1
  obtain ⟨M, -, -, -, hMae⟩ := hcap 0
  obtain ⟨s₃, θ₃, C₃, -, -, -, X₀, -, -, -, -, hae₀⟩ := armstrongDarioOrderZero_holds d hd p hpc hp1
  filter_upwards [hae₀, correctedPlaneExistence_holds hd p hpc hp1,
    orderOneDimension_le hd p hpc hp1, hMae] with ω hL hE hD hC h
  have hcapC : ∀ R : ℝ, ClusterBallCapDensity (uniqueInfiniteComponent h) 0 (M ω) R δ :=
    fun R => (hC h R).2
  have hslope0 : ∀ v : Fin d → ℝ,
      componentSlopeAsymptotics (uniqueInfiniteComponent h) v (fun _ => (0 : ℝ)) → v = 0 :=
    fun v hv => eq_zero_of_slopeAsymptotics_zero _ hδ hcapC hv
  obtain ⟨-, hL'⟩ := hL
  obtain ⟨hfin0, hrank0, -⟩ := hL' h
  -- the Liouville theorem of order zero
  have hliou : ∀ w : uniqueInfiniteComponent h → ℝ,
      (∀ x, componentLaplacian (uniqueInfiniteComponent h) w x = 0) →
      componentSlopeAsymptotics (uniqueInfiniteComponent h) 0 w → ∃ c : ℝ, ∀ x, w x = c := by
    intro w hharm hsub
    have hw : w ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 0 :=
      ⟨hharm, componentL2Subpolynomial_zero_of_slopeAsymptotics _ w hsub⟩
    obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfin0 hrank0 w hw
    exact ⟨c, fun x => congrFun hc x⟩
  -- normalized corrected planes
  have hnorm : ∀ (q : Fin d → ℝ) (o : uniqueInfiniteComponent h),
      ∃! u : uniqueInfiniteComponent h → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0 := by
    intro q o
    obtain ⟨u, hu⟩ := hE h q
    have hu' := isCorrectedPlane_sub (uniqueInfiniteComponent h) hu
      (isCorrectedPlane_const (uniqueInfiniteComponent h) (u o))
    rw [sub_zero] at hu'
    refine ⟨u - fun _ => u o, ⟨hu', by simp⟩, fun v ⟨hv, hvo⟩ => ?_⟩
    have hd' := isCorrectedPlane_sub (uniqueInfiniteComponent h) hv hu'
    rw [sub_self] at hd'
    obtain ⟨hharm, hslope⟩ :=
      (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mp hd'
    obtain ⟨c, hc⟩ := hliou _ hharm hslope
    have hc0 : c = 0 := by
      have := hc o
      simp only [Pi.sub_apply, hvo, sub_self] at this
      linarith
    funext x
    have := hc x
    rw [hc0] at this
    simp only [Pi.sub_apply] at this ⊢
    linarith
  refine ⟨hnorm, fun u hu => ?_⟩
  have : Infinite (uniqueInfiniteComponent h) :=
    Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨o⟩ := (inferInstance : Nonempty (uniqueInfiniteComponent h))
  -- uniqueness of the slope
  have huniq : ∀ q₁ q₂ : Fin d → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q₁ u →
      IsCorrectedPlane (uniqueInfiniteComponent h) q₂ u → q₁ = q₂ := by
    intro q₁ q₂ h₁ h₂
    have hd' := isCorrectedPlane_sub (uniqueInfiniteComponent h) h₁ h₂
    rw [sub_self] at hd'
    have hs := hd'.2
    have e : (fun _ : uniqueInfiniteComponent h => (0 : ℝ)) = 0 := rfl
    rw [← e] at hs
    exact sub_eq_zero.1 (hslope0 _ hs)
  -- the normalized corrected planes depend linearly on the slope
  set uq : (Fin d → ℝ) → uniqueInfiniteComponent h → ℝ := fun q =>
    Classical.choose (hnorm q o).exists with huqdef
  have huq : ∀ q, IsCorrectedPlane (uniqueInfiniteComponent h) q (uq q) ∧ uq q o = 0 :=
    fun q => Classical.choose_spec (hnorm q o).exists
  have hadd : ∀ q q', uq (q + q') = uq q + uq q' := fun q q' =>
    (hnorm (q + q') o).unique (huq (q + q'))
      ⟨isCorrectedPlane_add _ (huq q).1 (huq q').1, by simp [(huq q).2, (huq q').2]⟩
  have hsmul : ∀ (c : ℝ) q, uq (c • q) = c • uq q := fun c q =>
    (hnorm (c • q) o).unique (huq (c • q))
      ⟨isCorrectedPlane_smul _ (huq q).1 c, by simp [(huq q).2]⟩
  let Φ : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] (uniqueInfiniteComponent h → ℝ) :=
    { toFun := fun qa => uq qa.1 + fun _ => qa.2
      map_add' := fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, hadd]
        funext x; simp only [Pi.add_apply]; ring
      map_smul' := fun c a => by
        simp only [Prod.smul_fst, Prod.smul_snd, hsmul, RingHom.id_apply]
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring }
  have hmem : ∀ a, Φ a ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 := fun a =>
    add_mem (huq a.1).1.1 (const_mem_harmonicGrowthSpace _ 1 a.2)
  let Ψ := LinearMap.codRestrict (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) Φ hmem
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hΦ : uq a.1 + (fun _ => a.2) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Ψ, Φ] using this
    have hcp := isCorrectedPlane_add (uniqueInfiniteComponent h) (huq a.1).1
      (isCorrectedPlane_const (uniqueInfiniteComponent h) a.2)
    rw [add_zero, hΦ] at hcp
    have hq : a.1 = 0 := hslope0 _ hcp.2
    have hu0 : uq a.1 = 0 := by
      rw [hq]
      exact (hnorm 0 o).unique (huq 0) ⟨isCorrectedPlane_const _ 0, rfl⟩
    have ha2 : a.2 = 0 := by
      have := congrFun hΦ o
      simp only [Pi.add_apply, hu0, Pi.zero_apply, zero_add] at this
      exact this
    exact Prod.ext hq ha2
  obtain ⟨hfin, hrank⟩ := hD h
  have hdom : Module.finrank ℝ ((Fin d → ℝ) × ℝ) = d + 1 := by simp
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : Module.finrank ℝ ((Fin d → ℝ) × ℝ) =
      Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) := by omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  obtain ⟨a, ha⟩ := hsurj ⟨u, hu⟩
  have hua : u = uq a.1 + fun _ => a.2 := by
    have := congrArg Subtype.val ha
    simpa [Ψ, Φ] using this.symm
  have hcp := isCorrectedPlane_add (uniqueInfiniteComponent h) (huq a.1).1
    (isCorrectedPlane_const (uniqueInfiniteComponent h) a.2)
  rw [add_zero, ← hua] at hcp
  exact ⟨a.1, hcp, fun q hq => huniq q a.1 hq hcp⟩

end Rigidity.Proofs.Regularity.GeneralDim
