import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuMeasurable

/-!
# Quadratic minimization against a field pairing and a flux pairing, in every dimension

For a lattice edge field `g`, let
`ℓ_g u = ∑_{x ∈ U} ∑_i 1{x + e_i ∈ U} g(x, i) ([u](x + e_i) - [u](x))`
be the pairing of `g` with the gradient of the coarsening of `u` (for a constant field `q` this is
the coarse pairing `ℓ_q` of `μ`), and for a slope `p` let `F_p` be the flux pairing of `ν`. Set
`μ_{g,p}(U) = inf_{w ∈ A_*(U)} |U|⁻¹ (B(w, w)/2 - ℓ_g w - F_p w)`.

* On the partition event and for a resolved cube, `ℓ_g` vanishes on the null space of `B`, the
  first variation `B(w, u) = ℓ_g w + F_p w` (`w ∈ A_*(U)`) has a solution, and the infimum is
  attained at every solution (`cubeMuGen_eq_of_variation`).
* **Polarization.** If `u` solves the first variation of `μ_{g',p'}`, then for every field `g`,
  `ℓ_g u = -|U| (μ_{g+g',p'} - μ_{g,0} - μ_{g',p'})` (`cubeFieldPairing_eq_cubeMuGen`). With
  `g' = 0`, `u` is a maximizer of `ν(U, p')`.
* `μ_{g,p}(U)` depends only on the open edges inside `U` and the anchors of the partition cubes of
  the vertices of `U` (`cubeMuGen_eq_of_adj_iff_of_anchor_eq`), so
  `1{partition event, U resolved} μ_{g,p}(U)` is measurable (`measurable_cubeMuGen_indicator`).
  Hence the pairings of the maximizers of `ν` with any fixed field are measurable functions of the
  configuration, whatever maximizer is chosen.

This is the general-dimensional form of `Rigidity.Percolation.planarMuGen` and its properties.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω ω' : Configuration d}

/-- The pairing `ℓ_g u = ∑_{x ∈ U} ∑_i 1{x + e_i ∈ U} g(x, i) ([u](x + e_i) - [u](x))` of a lattice
edge field with the gradient of the coarsening. -/
noncomputable def cubeFieldPairing (ω : Configuration d) (U : TriadicCube d)
    (g : Vertex d → Fin d → ℝ) : Module.Dual ℝ (CubeFun ω U) :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
    if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
      g x i • (cubeEval ω U (partitionAnchor ω (x + LatticeProb.unit i)) -
        cubeEval ω U (partitionAnchor ω x))
    else 0

theorem cubeFieldPairing_apply {U : TriadicCube d} (g : Vertex d → Fin d → ℝ)
    (u : CubeFun ω U) :
    cubeFieldPairing ω U g u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
        g x i * (cubeExtend ω U u (partitionAnchor ω (x + LatticeProb.unit i)) -
          cubeExtend ω U u (partitionAnchor ω x))
      else 0 := by
  simp only [cubeFieldPairing, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, cubeEval_apply, smul_eq_mul]
  · simp

theorem cubeFieldPairing_add {U : TriadicCube d} (g h : Vertex d → Fin d → ℝ)
    (u : CubeFun ω U) :
    cubeFieldPairing ω U (g + h) u = cubeFieldPairing ω U g u + cubeFieldPairing ω U h u := by
  simp only [cubeFieldPairing_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

theorem cubeFieldPairing_zero_field {U : TriadicCube d} (u : CubeFun ω U) :
    cubeFieldPairing ω U 0 u = 0 := by
  rw [cubeFieldPairing_apply]
  simp

theorem cubeFluxPairing_zero_slope {U : TriadicCube d} (u : CubeFun ω U) :
    cubeFluxPairing ω U 0 u = 0 := by
  rw [cubeFluxPairing_apply]
  simp

/-- The field pairing vanishes on the null space of the Dirichlet form. -/
theorem cubeFieldPairing_eq_zero_of_cubeForm (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (g : Vertex d → Fin d → ℝ)
    {u : CubeFun ω U} (h : cubeForm ω U u u = 0) : cubeFieldPairing ω U g u = 0 := by
  rw [cubeFieldPairing_apply]
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hxi
  · have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
    have hxiU : x + LatticeProb.unit i ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hxi
    rw [cubeExtend_eq_of_cubeForm_self_eq_zero hd hP hU h
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hU hxiU)
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hU hxU)]
    ring
  · rfl

/-- The quantity `μ_{g,p}(U) = inf_{w ∈ A_*(U)} |U|⁻¹ (B(w, w)/2 - ℓ_g w - F_p w)`. -/
noncomputable def cubeMuGen (ω : Configuration d) (U : TriadicCube d)
    (g : Vertex d → Fin d → ℝ) (p : Fin d → ℝ) : ℝ :=
  ⨅ u : cubeHarmonic ω U,
    (cubeForm ω U u u / 2 - (cubeFieldPairing ω U g u + cubeFluxPairing ω U p u)) /
      U.latticeVolume

/-- **The infimum is attained at every solution of the first variation.** -/
theorem cubeMuGen_eq_of_variation {U : TriadicCube d} (g : Vertex d → Fin d → ℝ)
    (p : Fin d → ℝ) {u : CubeFun ω U} (hu : u ∈ cubeHarmonic ω U)
    (hfv : ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w u = cubeFieldPairing ω U g w + cubeFluxPairing ω U p w) :
    cubeMuGen ω U g p =
      (cubeForm ω U u u / 2 - (cubeFieldPairing ω U g u + cubeFluxPairing ω U p u)) /
        U.latticeVolume := by
  set Λ : Module.Dual ℝ (CubeFun ω U) := cubeFieldPairing ω U g + cubeFluxPairing ω U p with hΛ
  have hmin : ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U u u / 2 - Λ u ≤ cubeForm ω U w w / 2 - Λ w := fun w hw =>
    LinearMap.BilinForm.quadratic_le_of_apply_eq (cubeFormOn ω U)
      (fun u w => cubeForm_symm (u : CubeFun ω U) w)
      (fun v => cubeForm_self_nonneg (v : CubeFun ω U)) (Λ.comp (cubeHarmonic ω U).subtype)
      (u := ⟨u, hu⟩) (fun w' => hfv w'.1 w'.2) ⟨w, hw⟩
  have hvol := U.latticeVolume_pos
  set f : cubeHarmonic ω U → ℝ := fun w =>
    (cubeForm ω U w w / 2 - (cubeFieldPairing ω U g w + cubeFluxPairing ω U p w)) /
      U.latticeVolume with hf
  have hμ : cubeMuGen ω U g p = ⨅ w, f w := rfl
  have hle : ∀ w, (cubeForm ω U u u / 2 - (cubeFieldPairing ω U g u + cubeFluxPairing ω U p u)) /
      U.latticeVolume ≤ f w :=
    fun w => div_le_div_of_nonneg_right (hmin w.1 w.2) hvol.le
  have hfu : f ⟨u, hu⟩ =
      (cubeForm ω U u u / 2 - (cubeFieldPairing ω U g u + cubeFluxPairing ω U p u)) /
        U.latticeVolume := rfl
  rw [hμ]
  apply le_antisymm
  · rw [← hfu]
    exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨w, rfl⟩; rw [hfu]; exact hle w⟩ _
  · exact le_ciInf hle

/-- On the partition event and for a resolved cube, the first variation of `μ_{g,p}` has a
solution. -/
theorem exists_cubeMuGen_variation (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (g : Vertex d → Fin d → ℝ) (p : Fin d → ℝ) :
    ∃ u ∈ cubeHarmonic ω U, ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w u = cubeFieldPairing ω U g w + cubeFluxPairing ω U p w := by
  obtain ⟨u, hu, hmin⟩ := exists_cubeHarmonic_minimizer U
    (cubeFieldPairing ω U g + cubeFluxPairing ω U p) (fun v hv => by
      rw [LinearMap.add_apply, cubeFieldPairing_eq_zero_of_cubeForm hd hP hU g hv,
        cubeFluxPairing_eq_zero_of_cubeForm p hv, add_zero])
  exact ⟨u, hu, fun w hw => (hmin w hw).1⟩

/-- **Polarization.** If `u ∈ A_*(U)` solves the first variation of `μ_{g',p'}`, then for every
field `g`, `ℓ_g u = -|U| (μ_{g+g',p'} - μ_{g,0} - μ_{g',p'})`. -/
theorem cubeFieldPairing_eq_cubeMuGen (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) {g' : Vertex d → Fin d → ℝ} {p' : Fin d → ℝ}
    {u : CubeFun ω U} (hu : u ∈ cubeHarmonic ω U)
    (hfv : ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w u = cubeFieldPairing ω U g' w + cubeFluxPairing ω U p' w)
    (g : Vertex d → Fin d → ℝ) :
    cubeFieldPairing ω U g u = -U.latticeVolume *
      (cubeMuGen ω U (g + g') p' - cubeMuGen ω U g 0 - cubeMuGen ω U g' p') := by
  obtain ⟨v, hv, hfvv⟩ := exists_cubeMuGen_variation hd hP hU g 0
  have hvu : v + u ∈ cubeHarmonic ω U := add_mem hv hu
  have hfvs : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w (v + u) =
      cubeFieldPairing ω U (g + g') w + cubeFluxPairing ω U p' w := by
    intro w hw
    rw [map_add, hfvv w hw, hfv w hw, cubeFieldPairing_add, cubeFluxPairing_zero_slope]
    ring
  have h1 := cubeMuGen_eq_of_variation g 0 hv hfvv
  have h2 := cubeMuGen_eq_of_variation g' p' hu hfv
  have h3 := cubeMuGen_eq_of_variation (g + g') p' hvu hfvs
  have hvuB := hfv v hv
  have hsymm := cubeForm_symm (ω := ω) (U := U) u v
  have hexp : cubeForm ω U (v + u) (v + u) = cubeForm ω U v v + cubeForm ω U v u +
      (cubeForm ω U u v + cubeForm ω U u u) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [cubeFluxPairing_zero_slope] at h1
  rw [h1, h2, h3, hexp, cubeFieldPairing_add, map_add, map_add, map_add]
  have hvol := U.latticeVolume_pos.ne'
  have key : ∀ A B C : ℝ, -U.latticeVolume *
      (A / U.latticeVolume - B / U.latticeVolume - C / U.latticeVolume) = -(A - B - C) := by
    intro A B C
    field_simp
  rw [key]
  linear_combination (1 / 2 : ℝ) * hsymm + hvuB

section Transport

variable {U U' : TriadicCube d}
  (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))

/-- The flux pairing is invariant under a bijection of clusters respecting the open edges and
their displacements. -/
theorem cubeFluxPairing_comp_symm
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hdisp : ∀ x y i, ((e y).1 i : ℝ) - (e x).1 i = (y.1 i : ℝ) - x.1 i)
    (p : Fin d → ℝ) (u : CubeFun ω U) :
    cubeFluxPairing ω' U' p (u ∘ e.symm) = cubeFluxPairing ω U p u := by
  rw [cubeFluxPairing_apply, cubeFluxPairing_apply]
  congr 1
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.comp_apply, Equiv.symm_apply_apply, hadj, hdisp]

/-- **Relabelling invariance of `μ_{g,p}`.** A bijection of clusters which respects open edges,
their displacements and lattice interiors and carries the field pairing to the field pairing
preserves `μ_{g,p}`. -/
theorem cubeMuGen_eq_of_equiv
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hdisp : ∀ x y i, ((e y).1 i : ℝ) - (e x).1 i = (y.1 i : ℝ) - x.1 i)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hvol : U'.latticeVolume = U.latticeVolume) (g : Vertex d → Fin d → ℝ) (p : Fin d → ℝ)
    (hfield : ∀ u : CubeFun ω U,
      cubeFieldPairing ω' U' g (u ∘ e.symm) = cubeFieldPairing ω U g u) :
    cubeMuGen ω' U' g p = cubeMuGen ω U g p := by
  let E : cubeHarmonic ω U ≃ cubeHarmonic ω' U' :=
    { toFun := fun w => ⟨w.1 ∘ e.symm, (comp_symm_mem_cubeHarmonic_iff e hadj hint w.1).2 w.2⟩
      invFun := fun w => ⟨w.1 ∘ e, by
        apply (comp_symm_mem_cubeHarmonic_iff e hadj hint (w.1 ∘ e)).1
        have : (w.1 ∘ e) ∘ e.symm = w.1 := by
          funext y
          simp only [Function.comp_apply, Equiv.apply_symm_apply]
        rw [this]
        exact w.2⟩
      left_inv := fun w => by
        ext y
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
      right_inv := fun w => by
        ext y
        simp only [Function.comp_apply, Equiv.apply_symm_apply] }
  unfold cubeMuGen
  symm
  refine Equiv.iInf_congr E fun w => ?_
  change (cubeForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2 -
      (cubeFieldPairing ω' U' g (w.1 ∘ e.symm) + cubeFluxPairing ω' U' p (w.1 ∘ e.symm))) /
        U'.latticeVolume = _
  rw [cubeForm_comp_symm e hadj, hfield, cubeFluxPairing_comp_symm e hadj hdisp, hvol]

end Transport

/-- **Locality of `μ_{g,p}`.** `μ_{g,p}(U)` is determined by the open edges between vertices of
`U` and the anchors of the partition cubes of the vertices of `U`. -/
theorem cubeMuGen_eq_of_adj_iff_of_anchor_eq {U : TriadicCube d}
    (h : ∀ x ∈ U.vertices, ∀ y ∈ U.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y)
    (hanc : ∀ x ∈ U.vertices, partitionAnchor ω' x = partitionAnchor ω x)
    (g : Vertex d → Fin d → ℝ) (p : Fin d → ℝ) :
    cubeMuGen ω' U g p = cubeMuGen ω U g p := by
  have hC : ∀ x, x ∈ crossingClusterVertices ω U ↔ x ∈ crossingClusterVertices ω' U := by
    intro x
    rw [mem_crossingClusterVertices, mem_crossingClusterVertices,
      TriadicCube.crossingCluster_eq_of_adj_iff h]
  let e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U) :=
    Equiv.subtypeEquivRight hC
  have hext : ∀ (u : CubeFun ω U) (y : Vertex d),
      cubeExtend ω' U (u ∘ e.symm) y = cubeExtend ω U u y := by
    intro u y
    by_cases hy : y ∈ crossingClusterVertices ω U
    · rw [cubeExtend_apply_of_mem _ ((hC y).1 hy), cubeExtend_apply_of_mem _ hy]
      rfl
    · have hy' : y ∉ crossingClusterVertices ω' U := fun h' => hy ((hC y).2 h')
      change (if h : y ∈ crossingClusterVertices ω' U then (u ∘ e.symm) ⟨y, h⟩ else 0) =
        if h : y ∈ crossingClusterVertices ω U then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine cubeMuGen_eq_of_equiv e (fun x y => ?_) (fun x y i => rfl) (fun x => Iff.rfl) rfl g p
    fun u => ?_
  · exact (h x.1 (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 x.2)) y.1
      (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 y.2))).symm
  · rw [cubeFieldPairing_apply, cubeFieldPairing_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hanc _ ((U.mem_toIntegerCube_vertices _).1 hi),
        hanc _ ((U.mem_toIntegerCube_vertices _).1 hx), hext, hext]
    · rfl

/-- **Measurability of `μ_{g,p}`.** The quantity `1{partition event, V resolved} μ_{g,p}(V)` is
measurable. -/
theorem measurable_cubeMuGen_indicator (V : TriadicCube d) (g : Vertex d → Fin d → ℝ)
    (p : Fin d → ℝ) :
    Measurable fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g p else 0 := by
  set S := V.toIntegerCube.vertices
  let φ : Configuration d → Option (Finset (Vertex d × Vertex d) × (↥S → Vertex d)) :=
    fun ω => if PartitionEvent ω ∧ PartitionResolved ω V then
      some ((S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2),
        fun x => partitionAnchor ω x.1)
    else none
  have hE := measurableSet_partitionEvent_resolved V
  refine measurable_of_constant_on_fibres φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | ⟨E, a⟩
    · have heq : φ ⁻¹' {none} = {ω | PartitionEvent ω ∧ PartitionResolved ω V}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact hE.compl
    · have heq : φ ⁻¹' {some (E, a)} =
          {ω | PartitionEvent ω ∧ PartitionResolved ω V} ∩
            ({ω | (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2) = E} ∩
              ⋂ x : ↥S, {ω | PartitionEvent ω ∧ partitionAnchor ω x.1 = a x}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_iInter, φ]
        split_ifs with h
        · simp only [Option.some.injEq, Prod.mk.injEq, h, true_and, funext_iff]
        · simp only [h, false_and]
      rw [heq]
      refine hE.inter ((measurableSet_filter_eq (S ×ˢ S) E fun e =>
        measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)).inter ?_)
      exact MeasurableSet.iInter fun x => measurableSet_partitionAnchor_eq x.1 (a x)
  · by_cases hω : PartitionEvent ω ∧ PartitionResolved ω V
    · have hω' : PartitionEvent ω' ∧ PartitionResolved ω' V := by
        by_contra hn
        simp only [φ, if_pos hω, if_neg hn, reduceCtorEq] at h
      simp only [φ, if_pos hω, if_pos hω', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hAdj, hAnc⟩ := h
      rw [if_pos hω, if_pos hω']
      refine (cubeMuGen_eq_of_adj_iff_of_anchor_eq (fun x hx y hy => ?_) (fun x hx => ?_) g
        p).symm
      · have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx
        have hyS : y ∈ S := (V.mem_toIntegerCube_vertices y).2 hy
        have h2 := Finset.ext_iff.1 hAdj (x, y)
        simp only [Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
        exact h2
      · exact (congrFun hAnc ⟨x, (V.mem_toIntegerCube_vertices x).2 hx⟩).symm
    · have hω' : ¬ (PartitionEvent ω' ∧ PartitionResolved ω' V) := by
        intro hn
        simp only [φ, if_neg hω, if_pos hn, reduceCtorEq] at h
      rw [if_neg hω, if_neg hω']

end Rigidity.Percolation
