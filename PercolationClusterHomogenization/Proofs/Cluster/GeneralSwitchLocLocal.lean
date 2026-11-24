import PercolationClusterHomogenization.Proofs.Cluster.GeneralOneVarEst
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocal

/-!
# The localized pairing of display (5.31) of Armstrong and Dario, in every dimension

Let `V` be a triadic cube, `k` a scale with `k + 2 < scale V`, and `D` the inner cube of `V` at
distance `3^{k+2}` from its complement (`switchInterior`). On the event `CubeCapGood k V` that the
partition exists and agrees on `V` with the partition capped at scale `k`:

* the cubes of the capped partition at the vertices of `D`, the cubes deciding them and the
  partition cubes of the vertices of `D` lie inside `V`, so two configurations of the event with
  the same open edges inside `V` have the same partition cubes and anchors on `D`
  (`partitionAnchor_eq_of_cubeCapGood`);
* the crossing cluster `𝒞_*(V)` depends only on the open edges inside `V`.

The localized pairing `cubeSwitchLocValue` is `|V|⁻¹ ℓ_{g|D}(u_loc)`, where `u_loc` solves the first
variation with the field `q|D` (the local minimizer of Armstrong and Dario, proof of Lemma 5.7,
whose coarse pairing only reads the anchors on `D`); by polarization it is a combination of the
quantities `μ_{h,0}(V)` for fields `h` supported on the edges inside `D`, which depend only on the
cluster, the open edges inside `V` and the anchors on `D`
(`cubeMuGen_eq_of_adj_iff_of_anchor_eq_on`). It is therefore the same for two configurations of
the event with the same open edges inside `V` (`cubeSwitchLocValue_eq_of_cubeCapGood`). Its value at
a configuration of the event with the given open edges inside `V`, clamped to `[-M, M]`, is
measurable for the bonds inside `V` (`cubeSwitchLoc`), and these are independent for disjoint cubes
(`indepFun_cubeSwitchLoc`). The two-dimensional version is `Rigidity.Proofs.Cluster.switchLoc`.
-/

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω ω' : Configuration d}

/-- The partition exists and agrees on `V` with the partition capped at scale `k`. -/
def CubeCapGood (k : ℕ) (V : TriadicCube d) (ω : Configuration d) : Prop :=
  PartitionEvent ω ∧
    ∀ x ∈ V.vertices, partitionCube ω x = TriadicCube.cappedCube (TriadicCube.goodCubes ω) k x

theorem CubeCapGood.scale_le {k : ℕ} {V : TriadicCube d} (h : CubeCapGood k V ω) :
    ∀ x ∈ V.vertices, (partitionCube ω x).scale ≤ k := fun x hx => by
  rw [h.2 x hx]
  exact TriadicCube.scale_cappedCube_le _ _ _

theorem CubeCapGood.resolved {k : ℕ} {V : TriadicCube d} (h : CubeCapGood k V ω)
    (hk : k ≤ V.scale) : PartitionResolved ω V := fun x hx => (h.scale_le x hx).trans hk

/-- The open edges inside `V`. -/
noncomputable def cubeAdjData (V : TriadicCube d) (ω : Configuration d) :
    Finset (Vertex d × Vertex d) :=
  (V.toIntegerCube.vertices ×ˢ V.toIntegerCube.vertices).filter
    fun e => (openGraph ω).Adj e.1 e.2

theorem adj_iff_of_cubeAdjData_eq {V : TriadicCube d} (h : cubeAdjData V ω = cubeAdjData V ω') :
    ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := by
  intro x hx y hy
  have hxS : x ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices x).2 hx
  have hyS : y ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices y).2 hy
  have h2 := Finset.ext_iff.1 h (x, y)
  simp only [cubeAdjData, Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
  exact h2.symm

/-- The interior vertices used by the localized pairing: the inner cube of `V` at distance
`3^{k+2}` from its complement. -/
noncomputable def switchInterior (k : ℕ) (V : TriadicCube d) : Finset (Vertex d) :=
  (innerCube V (k + 2)).vertices

theorem switchInterior_subset {k : ℕ} {V : TriadicCube d} (hk : k + 2 < V.scale) :
    switchInterior k V ⊆ V.toIntegerCube.vertices :=
  innerCube_subset hk

/-- The points within `3^{k+2}` of the interior lie in `V`. -/
theorem mem_vertices_of_near_switchInterior {k : ℕ} {V : TriadicCube d} (hk : k + 2 < V.scale)
    {x y : Vertex d} (hx : x ∈ switchInterior k V) (hy : ∀ i, |y i - x i| ≤ 3 ^ (k + 2)) :
    y ∈ V.vertices := by
  rw [← V.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  unfold switchInterior at hx
  rw [IntegerCube.mem_vertices] at hx
  have hs := cast_innerCube_size hk
  intro i
  have h1 := hx i
  have h2 := hy i
  change V.toIntegerCube.corner i + 3 ^ (k + 2) ≤ x i ∧ x i < V.toIntegerCube.corner i +
    3 ^ (k + 2) + (((innerCube V (k + 2)).size : ℕ) : ℤ) at h1
  rw [hs] at h1
  change V.toIntegerCube.corner i ≤ y i ∧ y i < V.toIntegerCube.corner i + ((3 ^ V.scale : ℕ) : ℤ)
  push_cast
  rw [abs_le] at h2
  constructor <;> omega

/-- **Locality of the capped partition in the interior.** -/
theorem cappedCube_eq_of_adj_iff_switchInterior {k : ℕ} {V : TriadicCube d}
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hk : k + 2 < V.scale) {x : Vertex d} (hx : x ∈ switchInterior k V) :
    TriadicCube.cappedCube (TriadicCube.goodCubes ω') k x =
      TriadicCube.cappedCube (TriadicCube.goodCubes ω) k x := by
  refine TriadicCube.cappedCube_eq_of_agree fun T hT hnear => ?_
  have hsub : T.centeredTriple ⊆ V.vertices := by
    intro z hz
    refine mem_vertices_of_near_switchInterior hk hx fun i => ?_
    have h1 := hz i
    have h2 := hnear T.center T.center_mem i
    have hpow : 3 * T.side ≤ 3 ^ k := by
      calc 3 * T.side = (3 : ℤ) ^ (T.scale + 1) := by rw [TriadicCube.side, pow_succ]; ring
        _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hT
    have h9 : (3 : ℤ) ^ (k + 2) = 9 * 3 ^ k := by ring
    rw [abs_lt] at h1 h2
    rw [abs_le, h9]
    constructor <;> omega
  exact TriadicCube.mem_goodCubes_iff_of_adj_iff fun a ha b hb =>
    hagree a (hsub ha) b (hsub hb)

/-- **Locality of the partition cubes and anchors in the interior.** -/
theorem partitionAnchor_eq_of_cubeCapGood {k : ℕ} {V : TriadicCube d} (hω : CubeCapGood k V ω)
    (hω' : CubeCapGood k V ω')
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hk : k + 2 < V.scale) {x : Vertex d} (hx : x ∈ switchInterior k V) :
    partitionAnchor ω' x = partitionAnchor ω x := by
  have hxV : x ∈ V.vertices := (V.mem_toIntegerCube_vertices x).1 (switchInterior_subset hk hx)
  have hQ : partitionCube ω' x = partitionCube ω x := by
    rw [hω'.2 x hxV, hω.2 x hxV]
    exact cappedCube_eq_of_adj_iff_switchInterior hagree hk hx
  have hsub : (partitionCube ω x).vertices ⊆ V.vertices := by
    intro y hy
    refine mem_vertices_of_near_switchInterior hk hx fun i => ?_
    have h1 := TriadicCube.abs_coord_sub_lt_side (partitionCube_spec hω.1 x).1 hy i
    have h2 : (partitionCube ω x).side ≤ 3 ^ (k + 2) := by
      unfold TriadicCube.side
      exact pow_le_pow_right₀ (by norm_num) ((hω.scale_le x hxV).trans (by omega))
    rw [abs_sub_comm]
    linarith
  unfold partitionAnchor
  rw [hQ]
  exact TriadicCube.anchor_eq_of_adj_iff fun a ha b hb => hagree a (hsub ha) b (hsub hb)

/-- The field `g` restricted to the edges inside `D`. -/
noncomputable def cubeRestrictField (D : Finset (Vertex d)) (g : Vertex d → Fin d → ℝ) :
    Vertex d → Fin d → ℝ :=
  fun x i => if x ∈ D ∧ x + unit i ∈ D then g x i else 0

theorem cubeRestrictField_eq_zero {D : Finset (Vertex d)} (g : Vertex d → Fin d → ℝ)
    {x : Vertex d} {i : Fin d} (h : ¬(x ∈ D ∧ x + unit i ∈ D)) : cubeRestrictField D g x i = 0 := by
  simp only [cubeRestrictField, if_neg h]

/-- **Locality of `μ_{g,p}` for a field supported in `D`.** `μ_{g,p}(U)` is determined by the open
edges between vertices of `U` and the anchors of the partition cubes of the vertices of `D`, when
`g` vanishes off the edges inside `D`. -/
theorem cubeMuGen_eq_of_adj_iff_of_anchor_eq_on {U : TriadicCube d}
    (h : ∀ x ∈ U.vertices, ∀ y ∈ U.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y)
    {D : Finset (Vertex d)} (hanc : ∀ x ∈ D, partitionAnchor ω' x = partitionAnchor ω x)
    (g : Vertex d → Fin d → ℝ) (hg : ∀ x i, ¬(x ∈ D ∧ x + unit i ∈ D) → g x i = 0)
    (p : Fin d → ℝ) :
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
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · by_cases hD : x ∈ D ∧ x + unit i ∈ D
      · rw [hanc _ hD.2, hanc _ hD.1, hext, hext]
      · rw [hg x i hD, zero_mul, zero_mul]
    · rfl

/-- **The localized pairing** `|V|⁻¹ ℓ_{g|D}(u_loc)`, written through polarization: minus the
combination `μ_{g|D + q|D, 0} - μ_{g|D, 0} - μ_{q|D, 0}`. -/
noncomputable def cubeSwitchLocValue (k : ℕ) (V : TriadicCube d) (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) (ω : Configuration d) : ℝ :=
  if PartitionEvent ω ∧ PartitionResolved ω V then
    -(cubeMuGen ω V (cubeRestrictField (switchInterior k V) g +
          cubeRestrictField (switchInterior k V) (fun _ => q)) 0 -
        cubeMuGen ω V (cubeRestrictField (switchInterior k V) g) 0 -
        cubeMuGen ω V (cubeRestrictField (switchInterior k V) (fun _ => q)) 0)
  else 0

/-- **Locality of the localized pairing.** -/
theorem cubeSwitchLocValue_eq_of_cubeCapGood {k : ℕ} {V : TriadicCube d}
    (hω : CubeCapGood k V ω) (hω' : CubeCapGood k V ω') (hk : k + 2 < V.scale)
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (g : Vertex d → Fin d → ℝ) (q : Fin d → ℝ) :
    cubeSwitchLocValue k V g q ω' = cubeSwitchLocValue k V g q ω := by
  have hanc : ∀ x ∈ switchInterior k V, partitionAnchor ω' x = partitionAnchor ω x :=
    fun x hx => partitionAnchor_eq_of_cubeCapGood hω hω' hagree hk hx
  have hadj : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices,
      ((openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) := fun x hx y hy => (hagree x hx y hy).symm
  have hsupp : ∀ f : Vertex d → Fin d → ℝ, ∀ x i,
      ¬(x ∈ switchInterior k V ∧ x + unit i ∈ switchInterior k V) →
        cubeRestrictField (switchInterior k V) f x i = 0 :=
    fun f x i h => cubeRestrictField_eq_zero f h
  have e := fun f hf => cubeMuGen_eq_of_adj_iff_of_anchor_eq_on (U := V) hadj hanc f hf 0
  unfold cubeSwitchLocValue
  rw [if_pos ⟨hω'.1, hω'.resolved (by omega)⟩, if_pos ⟨hω.1, hω.resolved (by omega)⟩,
    e _ (hsupp _), e _ (hsupp _),
    e _ fun x i h => by rw [Pi.add_apply, Pi.add_apply, hsupp _ x i h, hsupp _ x i h, add_zero]]

/-- The value of the localized pairing at a configuration of the event with the given open edges
inside `V`. -/
noncomputable def cubeSwitchLocOf (k : ℕ) (V : TriadicCube d) (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) (t : Finset (Vertex d × Vertex d)) : ℝ :=
  if h : ∃ ω, CubeCapGood k V ω ∧ cubeAdjData V ω = t then cubeSwitchLocValue k V g q h.choose
  else 0

/-- **The local version of the pairing**, clamped to `[-M, M]`. -/
noncomputable def cubeSwitchLoc (k : ℕ) (V : TriadicCube d) (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) (M : ℝ) (ω : Configuration d) : ℝ :=
  max (-M) (min M (cubeSwitchLocOf k V g q (cubeAdjData V ω)))

theorem cubeSwitchLocOf_eq_of_cubeCapGood {k : ℕ} {V : TriadicCube d} (hω : CubeCapGood k V ω)
    (hk : k + 2 < V.scale) (g : Vertex d → Fin d → ℝ) (q : Fin d → ℝ) :
    cubeSwitchLocOf k V g q (cubeAdjData V ω) = cubeSwitchLocValue k V g q ω := by
  have h : ∃ ω', CubeCapGood k V ω' ∧ cubeAdjData V ω' = cubeAdjData V ω := ⟨ω, hω, rfl⟩
  rw [cubeSwitchLocOf, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact cubeSwitchLocValue_eq_of_cubeCapGood hω h1 hk (adj_iff_of_cubeAdjData_eq h2.symm) g q

theorem abs_cubeSwitchLoc_le {k : ℕ} {V : TriadicCube d} (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) {M : ℝ} (hM : 0 ≤ M) (ω : Configuration d) :
    |cubeSwitchLoc k V g q M ω| ≤ M := by
  unfold cubeSwitchLoc
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem cubeSwitchLoc_eq_of_cubeCapGood {k : ℕ} {V : TriadicCube d} (hω : CubeCapGood k V ω)
    (hk : k + 2 < V.scale) (g : Vertex d → Fin d → ℝ) (q : Fin d → ℝ) (M : ℝ) :
    cubeSwitchLoc k V g q M ω = max (-M) (min M (cubeSwitchLocValue k V g q ω)) := by
  rw [cubeSwitchLoc, cubeSwitchLocOf_eq_of_cubeCapGood hω hk]

theorem measurableSet_cubeAdjData_eq (V : TriadicCube d) (t : Finset (Vertex d × Vertex d)) :
    MeasurableSet (cubeAdjData V ⁻¹' {t}) :=
  measurableSet_filter_eq _ _ fun e => measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)

theorem measurable_cubeSwitchLoc (k : ℕ) (V : TriadicCube d) (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) (M : ℝ) : Measurable (cubeSwitchLoc k V g q M) :=
  measurable_of_constant_on_fibres (cubeAdjData V) (measurableSet_cubeAdjData_eq V) fun _ _ h => by
    simp only [cubeSwitchLoc, h]

/-- **Locality of the local version**: it is measurable for the bonds inside `V`. -/
theorem measurable_cubeSwitchLoc_localBondSigma (k : ℕ) (V : TriadicCube d)
    (g : Vertex d → Fin d → ℝ) (q : Fin d → ℝ) (M : ℝ) :
    Measurable[localBondSigma V.vertices] (cubeSwitchLoc k V g q M) :=
  measurable_localBondSigma_of_eq _ (measurable_cubeSwitchLoc k V g q M) fun ω ω' h => by
    have hagree := openGraph_adj_iff_of_localBonds h
    have hD : cubeAdjData V ω' = cubeAdjData V ω := by
      refine Finset.filter_congr fun e he => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
      exact hagree e.1 ((V.mem_toIntegerCube_vertices _).1 h1) e.2
        ((V.mem_toIntegerCube_vertices _).1 h2)
    simp only [cubeSwitchLoc, hD]

/-- **Independence of the local versions** on disjoint cubes. -/
theorem indepFun_cubeSwitchLoc (p : unitInterval) {k : ℕ} {V W : TriadicCube d}
    (hVW : Disjoint V.vertices W.vertices) (g g' : Vertex d → Fin d → ℝ) (q : Fin d → ℝ)
    (M : ℝ) :
    IndepFun (cubeSwitchLoc k V g q M) (cubeSwitchLoc k W g' q M) (latticeBondLaw d p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_cubeSwitchLoc_localBondSigma k V g q M).comap_le)
    (measurable_cubeSwitchLoc_localBondSigma k W g' q M).comap_le)

end Rigidity.Percolation
