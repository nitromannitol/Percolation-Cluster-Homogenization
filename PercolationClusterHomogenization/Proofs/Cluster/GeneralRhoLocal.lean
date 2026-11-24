import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaSupRate

/-!
# Local and stationary versions of `ρ(U)` in every dimension

The proof of Lemma 5.11 of Armstrong and Dario uses local versions `ρ_loc(U)` of
`ρ(U) = sup_q |q|⁻² ω(U, q)₊`, measurable with respect to the bonds near `U`, equal to `ρ(U)` off
an event of small probability, stationary, and independent for well separated cubes ((4.39) and
(4.40) of the source). The local data of the partition at `V` (`cubeLocalData`) determine
`1{P, V res} ν(V, ·)` and `1{P, V res} (-μ(V, ·))` on the good event `CubeLocalGood`
(`cubeNu_indicator_eq_of_cubeLocalData_eq`, `neg_cubeMu_indicator_eq_of_cubeLocalData_eq`), for
all slopes at once, so they determine `ρ(V)` (`cubeRho_eq_of_cubeLocalData_eq`); the local version
`cubeRhoLoc` is the value of `ρ(V)` at a configuration of the good event with the same local data.
It is measurable for the bonds inside `V.localRegion`, so that local versions on cubes with
disjoint regions are independent. The stationary version `cubeRhoStat` is the local version on the
cube of the same scale at the origin, at the translated configuration: it is exactly translation
covariant, its law does not depend on the position of the cube, and it equals `ρ(V)` on the good
event `CubeStatGood` (`cubeRhoStat_eq_of_good`). This is the general-dimensional form of
`Rigidity.Proofs.Cluster.planarRhoLoc` and `Rigidity.Proofs.Cluster.planarRhoStat`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω ω' : Configuration d}

/-- On the good events, the local data determine `1{P, V res} ν(V, ξ)`. -/
theorem cubeNu_indicator_eq_of_cubeLocalData_eq {V : TriadicCube d}
    (hω : CubeLocalGood ω V) (hω' : CubeLocalGood ω' V)
    (h : cubeLocalData ω V = cubeLocalData ω' V) (ξ : Fin d → ℝ) :
    (if PartitionEvent ω ∧ PartitionResolved ω V then cubeNu ω V ξ else 0) =
      if PartitionEvent ω' ∧ PartitionResolved ω' V then cubeNu ω' V ξ else 0 := by
  obtain ⟨hres, hadj, -⟩ := cubeLocalData_eq_imp hω hω' h
  by_cases hr : PartitionResolved ω V
  · rw [if_pos ⟨hω.1, hr⟩, if_pos ⟨hω'.1, hres.1 hr⟩, cubeNu_eq_of_adj_iff ξ hadj]
  · rw [if_neg fun h' => hr h'.2, if_neg fun h' => hr (hres.2 h'.2)]

/-- On the good events, the local data determine `1{P, V res} (-μ(V, q))`. -/
theorem neg_cubeMu_indicator_eq_of_cubeLocalData_eq {V : TriadicCube d}
    (hω : CubeLocalGood ω V) (hω' : CubeLocalGood ω' V)
    (h : cubeLocalData ω V = cubeLocalData ω' V) (q : Fin d → ℝ) :
    (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) =
      if PartitionEvent ω' ∧ PartitionResolved ω' V then -cubeMu ω' V q else 0 := by
  obtain ⟨hres, hadj, hanc⟩ := cubeLocalData_eq_imp hω hω' h
  by_cases hr : PartitionResolved ω V
  · rw [if_pos ⟨hω.1, hr⟩, if_pos ⟨hω'.1, hres.1 hr⟩,
      cubeMu_eq_of_adj_iff_of_anchor_eq hadj hanc q]
  · rw [if_neg fun h' => hr h'.2, if_neg fun h' => hr (hres.2 h'.2)]

/-- `ρ` is determined by the indicators of `ν` and `-μ`. -/
theorem cubeRho_eq_of_indicator_eq (p : unitInterval) {V V' : TriadicCube d}
    (hν : ∀ ξ, (if PartitionEvent ω ∧ PartitionResolved ω V then cubeNu ω V ξ else 0) =
      if PartitionEvent ω' ∧ PartitionResolved ω' V' then cubeNu ω' V' ξ else 0)
    (hμ : ∀ q, (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) =
      if PartitionEvent ω' ∧ PartitionResolved ω' V' then -cubeMu ω' V' q else 0) :
    cubeRho p ω V = cubeRho p ω' V' := by
  have hω : ∀ q, cubeOmega p ω V q = cubeOmega p ω' V' q := fun q => by
    simp only [cubeOmega, hν, hμ]
  unfold cubeRho
  simp only [hω]

/-- On the good events, the local data determine `ρ(V)`. -/
theorem cubeRho_eq_of_cubeLocalData_eq (p : unitInterval) {V : TriadicCube d}
    (hω : CubeLocalGood ω V) (hω' : CubeLocalGood ω' V)
    (h : cubeLocalData ω V = cubeLocalData ω' V) : cubeRho p ω V = cubeRho p ω' V :=
  cubeRho_eq_of_indicator_eq p (cubeNu_indicator_eq_of_cubeLocalData_eq hω hω' h)
    (neg_cubeMu_indicator_eq_of_cubeLocalData_eq hω hω' h)

/-- The value of `ρ(V)` at a configuration of the good event with given local data. -/
noncomputable def cubeRhoLocOf (p : unitInterval) (V : TriadicCube d) (t : CubeLocalDatum V) :
    ℝ :=
  if h : ∃ ω, CubeLocalGood ω V ∧ cubeLocalData ω V = t then cubeRho p h.choose V else 0

/-- **The local version of `ρ(V)`.** -/
noncomputable def cubeRhoLoc (p : unitInterval) (V : TriadicCube d) (ω : Configuration d) : ℝ :=
  cubeRhoLocOf p V (cubeLocalData ω V)

/-- **Agreement with `ρ`** on the good event. -/
theorem cubeRhoLoc_eq_of_good (p : unitInterval) {V : TriadicCube d} (hω : CubeLocalGood ω V) :
    cubeRhoLoc p V ω = cubeRho p ω V := by
  have hex : ∃ ω', CubeLocalGood ω' V ∧ cubeLocalData ω' V = cubeLocalData ω V :=
    ⟨ω, hω, rfl⟩
  unfold cubeRhoLoc cubeRhoLocOf
  rw [dif_pos hex]
  exact cubeRho_eq_of_cubeLocalData_eq p hex.choose_spec.1 hω hex.choose_spec.2

theorem cubeRhoLoc_nonneg (hd : 0 < d) (p : unitInterval) (V : TriadicCube d)
    (ω : Configuration d) : 0 ≤ cubeRhoLoc p V ω := by
  unfold cubeRhoLoc cubeRhoLocOf
  split_ifs
  · exact cubeRho_nonneg hd _ _ _
  · exact le_rfl

theorem measurable_cubeRhoLoc (p : unitInterval) (V : TriadicCube d) :
    Measurable (cubeRhoLoc p V) :=
  measurable_of_constant_on_fibres (fun ω => cubeLocalData ω V)
    (fun t => measurableSet_cubeLocalData_eq V t) fun _ _ h => congrArg (cubeRhoLocOf p V) h

/-- **Locality of `ρ_loc`**: it is measurable for the bonds inside the local region of `V`. -/
theorem measurable_cubeRhoLoc_localBondSigma (p : unitInterval) (V : TriadicCube d) :
    Measurable[localBondSigma V.localRegion] (cubeRhoLoc p V) :=
  measurable_localBondSigma_of_eq _ (measurable_cubeRhoLoc p V) fun _ _ h =>
    congrArg (cubeRhoLocOf p V) (cubeLocalData_eq_of_localBonds h).symm

/-- On the good events, translating the configuration and the cube by a multiple of the side
preserves `1{P, V res} ν(V, ξ)`. -/
theorem cubeNu_indicator_shift_eq_of_good {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) (hω : CubeLocalGood ω V)
    (hω' : CubeLocalGood (configurationTranslation z ω) (V.shift z)) (ξ : Fin d → ℝ) :
    (if PartitionEvent (configurationTranslation z ω) ∧
        PartitionResolved (configurationTranslation z ω) (V.shift z) then
      cubeNu (configurationTranslation z ω) (V.shift z) ξ else 0) =
      if PartitionEvent ω ∧ PartitionResolved ω V then cubeNu ω V ξ else 0 := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, partitionCube (configurationTranslation z ω) (x + z) =
      (partitionCube ω x).shift z := by
    intro x hx
    rw [partitionCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      partitionCube_eq_cappedCube hω hx]
    exact cappedCube_goodCubes_translation hz' ω x
  by_cases hres : PartitionResolved ω V
  · have hres' := (partitionResolved_shift_iff hz hpart).2 hres
    rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩, cubeNu_shift ω hz ξ]
  · have hres' : ¬ PartitionResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((partitionResolved_shift_iff hz hpart).1 h)
    rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]

/-- On the good events, translating the configuration and the cube by a multiple of the side
preserves `1{P, V res} (-μ(V, q))`. -/
theorem neg_cubeMu_indicator_shift_eq_of_good {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) (hω : CubeLocalGood ω V)
    (hω' : CubeLocalGood (configurationTranslation z ω) (V.shift z)) (q : Fin d → ℝ) :
    (if PartitionEvent (configurationTranslation z ω) ∧
        PartitionResolved (configurationTranslation z ω) (V.shift z) then
      -cubeMu (configurationTranslation z ω) (V.shift z) q else 0) =
      if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0 := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, partitionCube (configurationTranslation z ω) (x + z) =
      (partitionCube ω x).shift z := by
    intro x hx
    rw [partitionCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      partitionCube_eq_cappedCube hω hx]
    exact cappedCube_goodCubes_translation hz' ω x
  by_cases hres : PartitionResolved ω V
  · have hres' := (partitionResolved_shift_iff hz hpart).2 hres
    rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩,
      cubeMu_shift_translation_of_partition hres hz hpart q]
  · have hres' : ¬ PartitionResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((partitionResolved_shift_iff hz hpart).1 h)
    rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]

/-- **The stationary local version of `ρ(V)`**: the local version on the cube of the same scale
at the origin, at the configuration translated by `-center V`. -/
noncomputable def cubeRhoStat (p : unitInterval) (V : TriadicCube d) (ω : Configuration d) : ℝ :=
  cubeRhoLoc p V.atOrigin (configurationTranslation (-V.center) ω)

/-- **Exact translation covariance.** -/
theorem cubeRhoStat_shift (p : unitInterval) {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) (ω : Configuration d) :
    cubeRhoStat p (V.shift z) (configurationTranslation z ω) = cubeRhoStat p V ω := by
  unfold cubeRhoStat
  rw [TriadicCube.atOrigin_shift, configurationTranslation_add,
    TriadicCube.center_shift_eq_add hz, neg_add, neg_add_cancel_right]

theorem measurable_cubeRhoStat (p : unitInterval) (V : TriadicCube d) :
    Measurable (cubeRhoStat p V) :=
  (measurable_cubeRhoLoc p _).comp (configurationTranslationMeasurableEquiv _).measurable

theorem cubeRhoStat_nonneg (hd : 0 < d) (p : unitInterval) (V : TriadicCube d)
    (ω : Configuration d) : 0 ≤ cubeRhoStat p V ω :=
  cubeRhoLoc_nonneg hd p _ _

/-- **Stationarity in law** of `ρ_stat` (Armstrong and Dario, (4.40)). -/
theorem map_cubeRhoStat_shift (p : unitInterval) {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) :
    (latticeBondLaw d p).map (cubeRhoStat p (V.shift z)) =
      (latticeBondLaw d p).map (cubeRhoStat p V) := by
  have hmp := measurePreserving_configurationTranslation p z
  have h : cubeRhoStat p V = cubeRhoStat p (V.shift z) ∘ configurationTranslation z :=
    funext fun ω => (cubeRhoStat_shift p hz ω).symm
  rw [h, ← Measure.map_map (measurable_cubeRhoStat p _) hmp.measurable, hmp.map_eq]

/-- **Locality of `ρ_stat`.** -/
theorem measurable_cubeRhoStat_localBondSigma (p : unitInterval) (V : TriadicCube d) :
    Measurable[localBondSigma V.localRegion] (cubeRhoStat p V) :=
  measurable_localBondSigma_of_eq _ (measurable_cubeRhoStat p V) fun _ _ h =>
    congrArg (cubeRhoLocOf p V.atOrigin)
      (cubeLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds_atOrigin h)).symm

/-- **Agreement with `ρ`** on the good event of the stationary versions. -/
theorem cubeRhoStat_eq_of_good (p : unitInterval) {V : TriadicCube d}
    (h : CubeStatGood ω V) : cubeRhoStat p V ω = cubeRho p ω V := by
  unfold cubeRhoStat
  rw [cubeRhoLoc_eq_of_good p h.2]
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : CubeLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.atOrigin.shift V.center) := by
    rw [hω, V.atOrigin_shift_center]
    exact h.1
  have hν := cubeNu_indicator_shift_eq_of_good V.atOrigin_side_dvd_center h.2 h2
  have hμ := neg_cubeMu_indicator_shift_eq_of_good V.atOrigin_side_dvd_center h.2 h2
  rw [hω, V.atOrigin_shift_center] at hν hμ
  exact (cubeRho_eq_of_indicator_eq p hν hμ).symm

theorem localBonds_subset_localBonds {U W : Set (Vertex d)} (h : U ⊆ W) :
    localBonds U ⊆ localBonds W :=
  fun _ he x hx => h (he x hx)

/-- **Independence of stationary local versions over pairwise disjoint regions**: for cubes with
pairwise disjoint local regions, a function of `ρ_stat` at one cube is independent of the sum of
the same function over any set of the others. -/
theorem indepFun_comp_cubeRhoStat_sum (p : unitInterval) {ι : Type*} (V : ι → TriadicCube d)
    {g : ℝ → ℝ} (hg : Measurable g) {s : Finset ι}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (V i).localRegion (V j).localRegion)
    {i : ι} (hi : i ∈ s) {T : Finset ι} (hT : T ⊆ s) (hiT : i ∉ T) :
    IndepFun (fun ω => g (cubeRhoStat p (V i) ω))
      (fun ω => ∑ j ∈ T, g (cubeRhoStat p (V j) ω)) (latticeBondLaw d p) := by
  set R : Set (Vertex d) := ⋃ j ∈ T, (V j).localRegion with hR
  have hdR : Disjoint (V i).localRegion R := by
    rw [hR, Set.disjoint_iUnion_right]
    intro j
    rw [Set.disjoint_iUnion_right]
    intro hj
    exact hdisj i hi j (hT hj) fun h => hiT (h ▸ hj)
  have hmi : Measurable[localBondSigma (V i).localRegion]
      (fun ω => g (cubeRhoStat p (V i) ω)) :=
    hg.comp (measurable_cubeRhoStat_localBondSigma p (V i))
  have hmT : Measurable[localBondSigma R] (fun ω => ∑ j ∈ T, g (cubeRhoStat p (V j) ω)) := by
    refine measurable_localBondSigma_of_eq _ (Finset.measurable_sum T fun j _ =>
      hg.comp (measurable_cubeRhoStat p (V j))) fun ω ω' h => Finset.sum_congr rfl fun j hj => ?_
    have hsub : (V j).localRegion ⊆ R := by
      rw [hR]
      exact fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩
    exact congrArg (fun t => g (cubeRhoLocOf p (V j).atOrigin t))
      (cubeLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds_atOrigin
        fun e he => h e (localBonds_subset_localBonds hsub he))).symm
  exact (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hdR) hmi.comap_le) hmT.comap_le)

end Rigidity.Percolation
