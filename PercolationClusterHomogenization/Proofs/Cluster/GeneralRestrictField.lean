import PercolationClusterHomogenization.Proofs.Cluster.GeneralRestrictQuadCoarsen

/-!
# Lemma 5.5 of Armstrong and Dario for the pairings with a bounded field, in every dimension

The form of Lemma 5.5 used in Step 3 of the proof of Lemma 5.7 of Armstrong and Dario: the
pairing of the coarsened gradients with a bounded lattice field `g`, `|g| ≤ G`, instead of a
constant direction. For a triadic cube `U` and the subcubes `V` of scale `n`, the quantity

`N⁻¹ ∑_V (|V|⁻¹ (⟨∇[u_U]_𝒫, g⟩_V - ⟨∇[u_V]_𝒫, g⟩_V))²` (`cubeRestrictFieldError`),

`N` the number of subcubes, is on a resolved subcube the pairing of `g` with the coarsened gradient
of `w_V = u_U|_V - u_V` (`latticeEdgePairing_coarsen_sub_coarsen`). The proof of Lemma 5.5 for the
directions `eᵢ` applies with the factor `G²` in place of the number `d` of directions:

* on the good event of the reverse Hölder partition, the per-subcube bound of Steps 2 and 3 gives
  the quantity at most `G² Λ₀ D_n(U, q) / |U|` (`cubeMuRestrictFieldError_le_of_not_mem_cubeRestrictBad`);
* by the Cauchy–Schwarz inequality the quantity is at most `4d G² |U|⁻¹` times the energies of the
  coarsenings, hence at most `G²` times the majorant `16 d² K⁴ |q|² S(U)² / |U|` of the quantity
  for the directions (`cubeMuRestrictFieldError_le_sizeSum`), whose second moment is
  `O(G⁴ |q|⁴ |U|²)` (`exists_cubeMuRestrictFieldError_majorant`);
* the bad event has probability `O(3^{-(4d+1) n})` and Lemma 5.4 bounds the energy of the
  differences.

Hence for `2d ≤ n < m ≤ 2n`,
`E[cubeMuRestrictFieldError(□_m, n, q, g)] ≤ C G² |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`
(`exists_lintegral_cubeMuRestrictFieldError_le`). The two-dimensional version is
`Rigidity.Proofs.Cluster.exists_lintegral_planarMuRestrictFieldError_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
  Rigidity.Proofs.Cluster.GeneralDim
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **The quantity of Lemma 5.5 for a field** `g`, for a function `u_U` on `𝒞_*(U)` and functions
`u_V` on the clusters of the subcubes of scale `n`. -/
noncomputable def cubeRestrictFieldError (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (g : Vertex d → Fin d → ℝ) (uU : CubeFun ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V) : ℝ :=
  ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n,
    ((latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
      latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (uV V) (partitionAnchor ω x))) / V.latticeVolume) ^ 2

/-- **The quantity of Lemma 5.5 for a field and the minimizers of `μ`.** -/
noncomputable def cubeMuRestrictFieldError (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (q : Fin d → ℝ) (g : Vertex d → Fin d → ℝ) : ℝ :=
  cubeRestrictFieldError ω U n g (cubeMuMinimizer ω U q) fun V => cubeMuMinimizer ω V q

theorem cubeRestrictFieldError_nonneg (U : TriadicCube d) (n : ℕ) (g : Vertex d → Fin d → ℝ)
    (uU : CubeFun ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V) :
    0 ≤ cubeRestrictFieldError ω U n g uU uV :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem latticeEdgePairing_sub_right (D : Finset (Vertex d)) (g : Vertex d → Fin d → ℝ)
    (f₁ f₂ : Vertex d → ℝ) :
    latticeEdgePairing D g f₁ - latticeEdgePairing D g f₂ = latticeEdgePairing D g (f₁ - f₂) := by
  unfold latticeEdgePairing
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.sub_apply]
    ring
  · ring

/-- On a resolved cube `V`, the difference of the pairings of a field with the coarsened gradients
of a function on the cluster of `U` and of a function on the cluster of `V` is the pairing with the
coarsened gradient of the difference of the restriction and the function on `V`. -/
theorem latticeEdgePairing_coarsen_sub_coarsen (hd : 0 < d) (hP : PartitionEvent ω)
    {U V : TriadicCube d} (hVr : PartitionResolved ω V) (uU : CubeFun ω U) (v : CubeFun ω V)
    (g : Vertex d → Fin d → ℝ) :
    latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
      latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V v (partitionAnchor ω x)) =
      latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeRestrictExt V uU - v) (partitionAnchor ω x)) := by
  have hco : ∀ y ∈ V.toIntegerCube.vertices, cubeExtend ω U uU (partitionAnchor ω y) =
      cubeExtend ω V (cubeRestrictExt V uU) (partitionAnchor ω y) := by
    intro y hy
    have hyV := (V.mem_toIntegerCube_vertices y).1 hy
    have hmem : partitionAnchor ω y ∈ crossingClusterVertices ω V :=
      mem_crossingClusterVertices.2 (partitionAnchor_mem_crossingCluster_of_resolved hd hP hVr hyV)
    rw [cubeExtend_cubeRestrictExt V uU hmem]
  have h1 : latticeEdgePairing V.toIntegerCube.vertices g
      (fun x => cubeExtend ω U uU (partitionAnchor ω x)) =
      latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeRestrictExt V uU) (partitionAnchor ω x)) := by
    unfold latticeEdgePairing
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hxk
    · dsimp only
      rw [hco x hx, hco _ hxk]
    · rfl
  rw [h1, latticeEdgePairing_sub_right]
  congr 1
  funext x
  simp only [Pi.sub_apply, map_sub]

theorem restrictQuadConst_eq_sq_mul (d n j : ℕ) (G A CM p W : ℝ) :
    restrictQuadConst d n j G A CM p W = G ^ 2 * restrictQuadConst d n j 1 A CM p W := by
  unfold restrictQuadConst
  ring

/-- **The quantity of Lemma 5.5 for a field on the good event** (deterministic part, every
dimension `d ≥ 1`). -/
theorem cubeRestrictFieldError_le_of_good (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j) (uU : CubeFun ω U)
    (uV : ∀ V : TriadicCube d, CubeFun ω V) {g : Vertex d → Fin d → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) {ε r CM A W : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex d → ℝ) (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    (hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A)
    (hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V))) ^ (1 + ε / 2)) :
    cubeRestrictFieldError ω U n g uU uV ≤
      2 * (restrictQuadConst d n j G A CM (1 + ε / 2) W / ((3 : ℝ) ^ n) ^ d) *
        ((∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
          (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume) := by
  set Λ := restrictQuadConst d n j G A CM (1 + ε / 2) W with hΛ
  have hN := card_subcubesAt_mul_general U hn
  have hvolU := U.latticeVolume_pos
  have hS : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hNpos : (0 : ℝ) < (U.subcubesAt n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (U.subcubesAt n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have hterm : ∀ V ∈ U.subcubesAt n,
      ((latticeEdgePairing V.toIntegerCube.vertices g
          (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
        latticeEdgePairing V.toIntegerCube.vertices g
          (fun x => cubeExtend ω V (uV V) (partitionAnchor ω x))) / V.latticeVolume) ^ 2 ≤
      (Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) * cubeForm ω V (cubeRestrictExt V uU - uV V)
        (cubeRestrictExt V uU - uV V) := by
    intro V hV
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hVU : V.vertices ⊆ U.vertices := TriadicCube.subset_of_mem_subcubesAt hn hV
    have hresV : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j := fun x hx => hres x (hVU hx)
    have hVr : PartitionResolved ω V := fun z hz => (hresV z hz).le.trans (by omega)
    have hWV : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W :=
      fun z hz => hW z (hVU ((V.mem_toIntegerCube_vertices z).1 (Finset.filter_subset _ _ hz)))
    have hvol : V.latticeVolume = ((3 : ℝ) ^ n) ^ d := by rw [TriadicCube.latticeVolume, hVs]
    have hcov : ∀ z ∈ partitionBoxCluster ω (innerCube V j), ∃ c ∈ midCubeCells V j,
        z ∈ cube c.1 c.2 := fun z hz => midCubeCells_cover V j (mem_partitionBoxCluster.1 hz).1
    have hb := latticeEdgePairing_cubeExtend_sq_le_cubeForm hd hP hVr (by omega : j < V.scale)
      hresV (cubeRestrictExt V uU - uV V) hg Wt hWt hWV hpq hCM hA0 (midCubeCells V j)
      (N := 3 ^ d) hcov (fun c hc => midCubeCells_enl_subset hj1 (by omega) hc)
      (fun x => card_midCubeCells_filter_le V j x) (hA V hV) (hM V hV)
    rw [hVs] at hb
    rw [latticeEdgePairing_coarsen_sub_coarsen hd hP hVr uU (uV V) g, div_pow, hvol,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    refine hb.trans (le_of_eq ?_)
    rw [hΛ, restrictQuadConst]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hfinal : ((U.subcubesAt n).card : ℝ)⁻¹ * ((Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) *
      ∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
        (cubeRestrictExt V uU - uV V)) =
      2 * (Λ / ((3 : ℝ) ^ n) ^ d) * ((∑ V ∈ U.subcubesAt n,
        cubeForm ω V (cubeRestrictExt V uU - uV V) (cubeRestrictExt V uU - uV V) / 2) /
          U.latticeVolume) := by
    rw [← Finset.sum_div, ← hN]
    field_simp
  unfold cubeRestrictFieldError
  calc ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n,
        ((latticeEdgePairing V.toIntegerCube.vertices g
            (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
          latticeEdgePairing V.toIntegerCube.vertices g
            (fun x => cubeExtend ω V (uV V) (partitionAnchor ω x))) / V.latticeVolume) ^ 2
      ≤ ((U.subcubesAt n).card : ℝ)⁻¹ * ((Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) *
          ∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
            (cubeRestrictExt V uU - uV V)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
    _ = _ := hfinal

theorem restrictQuadConst_nonneg {n j : ℕ} {A CM p W : ℝ} (hA : 0 ≤ A) (hCM : 0 ≤ CM)
    (hW : 0 ≤ W) : 0 ≤ restrictQuadConst d n j 1 A CM p W := by
  unfold restrictQuadConst
  have := Real.rpow_nonneg hCM (1 / p)
  positivity

/-- **Off the bad event, the quantity of Lemma 5.5 for a field is controlled by the energy of the
differences** (every dimension `d ≥ 1`), above the partition `𝓡` of Definition 3.7. -/
theorem cubeRestrictFieldError_le_of_not_mem_cubeRestrictBad (hd : 0 < d) {A₀ : ℝ}
    {s : Configuration d → Vertex d → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ) (hCM : 0 ≤ CM)
    (hAτ : 0 ≤ Aτ)
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    {ω : Configuration d} (hP : PartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    {U : TriadicCube d} {n : ℕ} (hn : 2 * d ≤ n) (hnm : n < U.scale)
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) (uU : CubeFun ω U)
    (huU : uU ∈ cubeHarmonic ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V)
    (huV : ∀ V ∈ U.subcubesAt n, uV V ∈ cubeHarmonic ω V) {g : Vertex d → Fin d → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) :
    cubeRestrictFieldError ω U n g uU uV ≤
      G ^ 2 * restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) *
        ((∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
          (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume) := by
  obtain ⟨hcell, hnb, hRH⟩ := hs
  set j := n / (2 * d) with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hjn : j < n := Nat.div_lt_self (by omega) (by omega)
  have h2dj : 2 * d * j ≤ n := Nat.mul_div_le n (2 * d)
  have hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j := fun x hx => by
    by_contra h
    exact hgood (Set.mem_union_left _
      ⟨hP, x, (U.mem_toIntegerCube_vertices x).2 hx, not_lt.1 h⟩)
  have hcells : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ ≤ Aτ * (cube c.1 c.2).card ∧
      (∀ z ∈ enl 1 c.1 c.2, s ω z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube c.1 c.2).card := by
    intro V hV c hc
    have hnot : ω ∉ ({ω | Aτ * (cube c.1 c.2).card <
          ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}) := fun h =>
      hgood (Set.mem_union_right _ (Set.mem_iUnion₂.2 ⟨V, hV, Set.mem_iUnion₂.2 ⟨c, hc, h⟩⟩))
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_exists, not_and] at hnot
    exact ⟨hnot.1, fun z hz => hnot.2.1 z hz, hnot.2.2⟩
  set Wt : Vertex d → ℝ := fun z => (3 : ℝ) ^ (partitionCube ω z).scale with hWtdef
  have hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z := fun z => le_rfl
  have hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ 3 ^ j := fun z hz =>
    pow_le_pow_right₀ (by norm_num) (hres z hz).le
  have hr0 : 0 < r := hpq.symm.pos
  have hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ Aτ ^ (1 / r) := by
    intro V hV c hc
    have hsum := (hcells V hV c hc).1
    have hpt : ∀ x, (Wt x ^ (2 * d - 1)) ^ r ≤ ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ := by
      intro x
      have h1 : (1 : ℝ) ≤ Wt x := one_le_pow₀ (by norm_num)
      rw [← Real.rpow_natCast (Wt x) (2 * d - 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 hτr
    have hcpos := card_cube_pos c.1 c.2
    have havg : avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ≤ Aτ := by
      rw [avg, div_le_iff₀ hcpos]
      exact (Finset.sum_le_sum fun x _ => hpt x).trans hsum
    have havg0 : 0 ≤ avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) :=
      div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
        (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow havg0 havg (by positivity)
  have hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V))) ^ (1 + ε / 2) := by
    intro V hV c hc
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hVU : V.vertices ⊆ U.vertices := TriadicCube.subset_of_mem_subcubesAt hnm.le hV
    have hVr : PartitionResolved ω V := fun z hz =>
      (hres z (hVU hz)).le.trans (by omega)
    have hjV : j < V.scale := by omega
    have hw := sub_mem_cubeHarmonic_of_mem_subcubesAt hd hP hnm.le hV hVr huU (huV V hV)
    obtain ⟨-, hsk, hmom⟩ := hcells V hV c hc
    refine hMey ω (crossingClusterVertices ω V) (cubeExtend ω V (cubeRestrictExt V uU - uV V))
      c.1 c.2 (s ω) ?_ ?_ hcell hnb ?_ (fun k y hy _ => hRH k y hy) hmom
    · intro a ha b hadj hb
      have hbV : b ∈ V.vertices := (V.mem_toIntegerCube_vertices b).1
        (midCubeCells_enl_subset hj1 hjV hc hb)
      exact mem_crossingClusterVertices.2
        (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 ha) hbV hadj)
    · intro a ha haE hall
      exact openLaplacian_cubeExtend_eq_zero hw ha
        (midCubeCells_isLatticeInterior hj1 hjV hc haE) hall
    · intro z hz
      exact (cube_mono (hsk z hz) z).trans (cube_subset_enl_of_mem hz)
  have h := cubeRestrictFieldError_le_of_good hd hP hj1 hjn hnm.le hres uU uV hg hpq hCM
    (Real.rpow_nonneg hAτ _) Wt hWt hW hA hM
  have hD0 : 0 ≤ (∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
      (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume :=
    div_nonneg (Finset.sum_nonneg fun V _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num))
      U.latticeVolume_pos.le
  have hconst := two_mul_restrictQuadConst_div_le hd h2dj (Real.rpow_nonneg hAτ (1 / r)) hCM
    (n := n) (j := j) (p := 1 + ε / 2)
  have hx0 : 0 ≤ restrictQuadConst d n j 1 (Aτ ^ (1 / r)) CM (1 + ε / 2) (3 ^ j) /
      ((3 : ℝ) ^ n) ^ d :=
    div_nonneg (restrictQuadConst_nonneg (Real.rpow_nonneg hAτ _) hCM (by positivity))
      (by positivity)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hle : 2 * (restrictQuadConst d n j G (Aτ ^ (1 / r)) CM (1 + ε / 2) (3 ^ j) /
      ((3 : ℝ) ^ n) ^ d) ≤ G ^ 2 * restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) := by
    rw [restrictQuadConst_eq_sq_mul, mul_div_assoc]
    have h2 : 2 * (restrictQuadConst d n j 1 (Aτ ^ (1 / r)) CM (1 + ε / 2) (3 ^ j) /
        ((3 : ℝ) ^ n) ^ d) ≤ restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) := by
      refine le_trans ?_ hconst
      nlinarith
    nlinarith [sq_nonneg G]
  exact h.trans (mul_le_mul_of_nonneg_right hle hD0)

/-- **Off the bad event, the quantity of Lemma 5.5 for a field and `μ` is controlled by
Lemma 5.4** (every dimension `d ≥ 1`), above the partition `𝓡` of Definition 3.7. -/
theorem cubeMuRestrictFieldError_le_of_not_mem_cubeRestrictBad (hd : 0 < d) {A₀ : ℝ}
    {s : Configuration d → Vertex d → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ) (hCM : 0 ≤ CM)
    (hAτ : 0 ≤ Aτ)
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    {ω : Configuration d} (hP : PartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    {U : TriadicCube d} {n : ℕ} (hn : 2 * d ≤ n) (hnm : n < U.scale)
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) (q : Fin d → ℝ) {g : Vertex d → Fin d → ℝ}
    {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) :
    cubeMuRestrictFieldError ω U n q g ≤
      G ^ 2 * restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) *
        (cubeMuDefect ω U n q / U.latticeVolume) := by
  have hres := scale_lt_of_not_mem_cubeRestrictBad hP hgood
  have hjn : n / (2 * d) < n := Nat.div_lt_self (by omega) (by omega)
  have hU : PartitionResolved ω U := fun z hz => (hres z hz).le.trans (by omega)
  have hVr : ∀ V ∈ U.subcubesAt n, PartitionResolved ω V := fun V hV z hz => by
    rw [TriadicCube.scale_of_mem_subcubesAt hV]
    exact (hres z (TriadicCube.subset_of_mem_subcubesAt hnm.le hV hz)).le.trans hjn.le
  have h := cubeRestrictFieldError_le_of_not_mem_cubeRestrictBad hd hpq hτr hCM hAτ hMey hP hs hn
    hnm hgood (cubeMuMinimizer ω U q) (cubeMuMinimizer_spec hd hP hU q).1
    (fun V => cubeMuMinimizer ω V q) (fun V hV => (cubeMuMinimizer_spec hd hP (hVr V hV) q).1) hg
  rw [cubeMuRestrictFieldError, cubeMuDefect, if_pos ⟨hP, hU⟩,
    resolvedSubcubesAt_eq_of_lt hjn hnm.le hres]
  exact h

/-- **Cauchy–Schwarz for the pairing with a bounded field**: `⟨∇f, g⟩_D² ≤ 2d G² |D| ∑_D |∇f|²_D`. -/
theorem latticeEdgePairing_sq_le_of_abs_le (D : Finset (Vertex d)) {g : Vertex d → Fin d → ℝ}
    {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (f : Vertex d → ℝ) :
    latticeEdgePairing D g f ^ 2 ≤
      2 * d * G ^ 2 * D.card * ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ 2 := by
  have h1 := latticeEdgePairing_sq_le D g f
  have h2 := sum_latticeEdge_sq_le D hg
  have h3 := latticeEdgeEnergy_le_two_mul_sum_gradNormIn_sq D f
  have h0 := latticeEdgeEnergy_nonneg D f
  calc latticeEdgePairing D g f ^ 2
      ≤ (∑ x ∈ D, ∑ k : Fin d, if x + LatticeProb.unit k ∈ D then g x k ^ 2 else 0) *
          latticeEdgeEnergy D f := h1
    _ ≤ (d * G ^ 2 * D.card) * (2 * ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ 2) :=
        mul_le_mul h2 h3 h0 (by positivity)
    _ = _ := by ring

/-- **The quantity of Lemma 5.5 for a field by the energies of the coarsenings.** -/
theorem cubeRestrictFieldError_le_energy {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G)
    (uU : CubeFun ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V) :
    cubeRestrictFieldError ω U n g uU uV ≤ 4 * d * G ^ 2 / U.latticeVolume *
      (∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
          U.toIntegerCube.vertices (fun x => cubeExtend ω U uU (partitionAnchor ω x)) x ^ 2 +
        ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
          V.toIntegerCube.vertices (fun x => cubeExtend ω V (uV V) (partitionAnchor ω x)) x ^ 2) :=
    by
  set fU : Vertex d → ℝ := fun x => cubeExtend ω U uU (partitionAnchor ω x) with hfU
  set fV : TriadicCube d → Vertex d → ℝ := fun V x => cubeExtend ω V (uV V) (partitionAnchor ω x)
    with hfV
  have hN := card_subcubesAt_mul_general U hn
  have hvolU := U.latticeVolume_pos
  have hNpos : (0 : ℝ) < (U.subcubesAt n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (U.subcubesAt n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hterm : ∀ V ∈ U.subcubesAt n,
      ((latticeEdgePairing V.toIntegerCube.vertices g fU -
        latticeEdgePairing V.toIntegerCube.vertices g (fV V)) / V.latticeVolume) ^ 2 ≤
      4 * d * G ^ 2 / ((3 : ℝ) ^ n) ^ d * (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices fU x ^ 2 +
        ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2) := by
    intro V hV
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hvol : V.latticeVolume = ((3 : ℝ) ^ n) ^ d := by rw [TriadicCube.latticeVolume, hVs]
    have hcard : (V.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ n) ^ d := by
      rw [V.card_toIntegerCube_vertices, hvol]
    set a := ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices fU x ^ 2 with ha
    set b := ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2 with hb
    have h1 := latticeEdgePairing_sq_le_of_abs_le V.toIntegerCube.vertices hg fU
    have h2 := latticeEdgePairing_sq_le_of_abs_le V.toIntegerCube.vertices hg (fV V)
    rw [hcard, ← ha] at h1
    rw [hcard, ← hb] at h2
    rw [div_pow, hvol, div_le_iff₀ (by positivity)]
    have e : 4 * d * G ^ 2 / ((3 : ℝ) ^ n) ^ d * (a + b) * (((3 : ℝ) ^ n) ^ d) ^ 2 =
        2 * (2 * d * G ^ 2 * ((3 : ℝ) ^ n) ^ d * a) +
          2 * (2 * d * G ^ 2 * ((3 : ℝ) ^ n) ^ d * b) := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (latticeEdgePairing V.toIntegerCube.vertices g fU +
      latticeEdgePairing V.toIntegerCube.vertices g (fV V))]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hU := sum_subcubesAt_sum_gradNormIn_sq_le hn fU
  set A := ∑ x ∈ U.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices fU x ^ 2 with hA
  set B := ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2 with hB
  have hG0 : 0 ≤ 4 * d * G ^ 2 / ((3 : ℝ) ^ n) ^ d := by positivity
  have hstep : ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n,
        ((latticeEdgePairing V.toIntegerCube.vertices g fU -
          latticeEdgePairing V.toIntegerCube.vertices g (fV V)) / V.latticeVolume) ^ 2 ≤
      ((U.subcubesAt n).card : ℝ)⁻¹ * (4 * d * G ^ 2 / ((3 : ℝ) ^ n) ^ d * (A + B)) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (inv_nonneg.2 hNpos.le)
    refine mul_le_mul_of_nonneg_left ?_ hG0
    linarith
  unfold cubeRestrictFieldError
  refine hstep.trans (le_of_eq ?_)
  rw [← hN]
  field_simp

/-- **A majorant of the quantity of Lemma 5.5 for a field and `μ` by the partition sizes**:
it is at most `G²` times the majorant `16 d² K⁴ |q|² S(U)² / |U|` of the quantity for the
directions. -/
theorem cubeMuRestrictFieldError_le_sizeSum (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ) {g : Vertex d → Fin d → ℝ}
    {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) :
    cubeMuRestrictFieldError ω U n q g ≤
      G ^ 2 * (16 * d ^ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 *
        (∑ i, q i ^ 2) * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 /
          U.latticeVolume) := by
  set c := 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 * (∑ i, q i ^ 2)
    with hc
  have hc0 : 0 ≤ c := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (q i)
    positivity
  set S := partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) with hS
  have h := cubeRestrictFieldError_le_energy (ω := ω) hn hg (cubeMuMinimizer ω U q)
    (fun V => cubeMuMinimizer ω V q)
  have hU := sum_gradNormIn_coarse_cubeMuMinimizer_le hd hP U q
  have hV : ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2 ≤
      c * S ^ 2 := by
    calc ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2
        ≤ ∑ V ∈ U.subcubesAt n, c * partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) ^ 2 :=
          Finset.sum_le_sum fun V _ => sum_gradNormIn_coarse_cubeMuMinimizer_le hd hP V q
      _ ≤ ∑ V ∈ U.subcubesAt n,
            c * (partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) * S) := by
          refine Finset.sum_le_sum fun V hVm => mul_le_mul_of_nonneg_left ?_ hc0
          rw [sq]
          refine mul_le_mul_of_nonneg_left ?_ (partitionSizeSum_nonneg _ _)
          rw [hS, ← sum_subcubesAt_partitionSizeSum hn]
          exact Finset.single_le_sum (f := fun V => partitionSizeSum ω V.toIntegerCube.vertices
            (2 * d - 1)) (fun V _ => partitionSizeSum_nonneg _ _) hVm
      _ = c * S ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, sum_subcubesAt_partitionSizeSum hn, ← hS]
          ring
  have hvol := U.latticeVolume_pos
  unfold cubeMuRestrictFieldError
  refine h.trans ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hS0 : 0 ≤ c * S ^ 2 := by positivity
  rw [div_mul_eq_mul_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hvol]
  have e : G ^ 2 * (16 * (d : ℝ) ^ 2 * (d * d * coarseGradConstant d ^ 2) *
      coarseGradConstant d ^ 2 * (∑ i, q i ^ 2) * S ^ 2) = 4 * d * G ^ 2 * (d * (2 * (c * S ^ 2))) := by
    rw [hc]
    ring
  rw [e]
  have hsum : (∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
      U.toIntegerCube.vertices (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
        (partitionAnchor ω x)) x ^ 2 +
      ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
        V.toIntegerCube.vertices (fun x => cubeExtend ω V (cubeMuMinimizer ω V q)
          (partitionAnchor ω x)) x ^ 2) ≤ d * (2 * (c * S ^ 2)) := by
    have h2 : 2 * (c * S ^ 2) ≤ d * (2 * (c * S ^ 2)) := le_mul_of_one_le_left (by positivity) hd1
    linarith
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **A measurable majorant of the quantity of Lemma 5.5 for a field and `μ` with a second
moment**: `E[M²] ≤ C G⁴ |q|⁴ |U|²`. -/
theorem exists_cubeMuRestrictFieldError_majorant [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale → ∀ (q : Fin d → ℝ)
      (g : Vertex d → Fin d → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
        (∀ᵐ ω ∂(latticeBondLaw d p), ENNReal.ofReal (cubeMuRestrictFieldError ω U n q g) ≤ M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p) ≤
          C * ENNReal.ofReal (G ^ 2 * ∑ i, q i ^ 2) ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set c : ℝ := 16 * d ^ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2
    with hc
  have hc0 : 0 ≤ c := by positivity
  set τ : ℕ := 4 * (2 * d - 1) with hτ
  set Cτ : ℝ := 2 * (τ.factorial : ℝ) * θ ^ τ with hCτ
  have hCτ0 : 0 ≤ Cτ := by positivity
  refine ⟨ENNReal.ofReal (c ^ 2 * Cτ), ENNReal.ofReal_ne_top, fun U n hn q g G hg => ?_⟩
  set P : ℝ := G ^ 2 * ∑ i, q i ^ 2 with hP
  have hP0 : 0 ≤ P := mul_nonneg (sq_nonneg G) (Finset.sum_nonneg fun i _ => sq_nonneg (q i))
  set N : ℝ := (U.toIntegerCube.vertices.card : ℝ) with hN
  have hNvol : N = U.latticeVolume := U.card_toIntegerCube_vertices
  have hN0 : 0 < N := by rw [hNvol]; exact U.latticeVolume_pos
  set M : Configuration d → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 / U.latticeVolume)
    with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp ((measurable_const.mul
      ((measurable_partitionSizeSum _ _).pow_const 2)).div_const _)
  · filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    refine ENNReal.ofReal_le_ofReal ((cubeMuRestrictFieldError_le_sizeSum hd0 hPω hn q hg).trans
      (le_of_eq ?_))
    rw [hP, hc]
    ring
  · have hint := (hmom τ U.toIntegerCube.vertices).1
    have hint2 := (hmom τ U.toIntegerCube.vertices).2
    have hpt : ∀ ω, M ω ^ 2 ≤ ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 *
        ∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) := by
      intro ω
      rw [hMdef]
      dsimp only
      rw [← ENNReal.ofReal_pow (by
        have := partitionSizeSum_nonneg (ω := ω) U.toIntegerCube.vertices (2 * d - 1)
        have := U.latticeVolume_pos
        positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h4 := partitionSizeSum_pow_four_le ω U.toIntegerCube.vertices (2 * d - 1)
      rw [← hNvol]
      have e : (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 / N) ^ 2 =
          (c * P / N) ^ 2 * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 4 := by
        ring
      rw [e]
      have hcp : 0 ≤ (c * P / N) ^ 2 := sq_nonneg _
      calc (c * P / N) ^ 2 * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 4
          ≤ (c * P / N) ^ 2 * (N ^ 3 * partitionSizeSum ω U.toIntegerCube.vertices
              (4 * (2 * d - 1))) := mul_le_mul_of_nonneg_left h4 hcp
        _ = (c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ := by
            rw [partitionSizeSum]
            ring
    calc ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)
        ≤ ∫⁻ ω, ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) ∂(latticeBondLaw d p) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (∫ ω, (c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ ∂(latticeBondLaw d p)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (ae_of_all _ fun ω => mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ =>
              pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _))).symm
      _ ≤ ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 * (Cτ * N)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hint2 (by positivity)
      _ = ENNReal.ofReal (c ^ 2 * Cτ) * ENNReal.ofReal P ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
          have e : (c * P / N) ^ 2 * N ^ 3 * (Cτ * N) = c ^ 2 * Cτ * P ^ 2 * N ^ 2 := by
            field_simp
          rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow hP0, ENNReal.ofReal_pow hN0.le, hN, ENNReal.ofReal_natCast]

/-- **Lemma 5.5 of Armstrong and Dario for the pairings with a bounded field** (the form used in
Step 3 of the proof of Lemma 5.7, every dimension `d ≥ 2`, `p > p_c(d)`): for `2d ≤ n < m ≤ 2n` and
a field `g` with `|g| ≤ G`,
`E[cubeMuRestrictFieldError(□_m, n, q, g)] ≤ C G² |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`. -/
theorem exists_lintegral_cubeMuRestrictFieldError_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (q : Fin d → ℝ) (g : Vertex d → Fin d → ℝ) (G : ℝ),
      (∀ x i, |g x i| ≤ G) → 2 * d ≤ n → n < m → m ≤ 2 * n →
      ∫⁻ ω, ENNReal.ofReal (cubeMuRestrictFieldError ω ⟨m, 0⟩ n q g) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (G ^ 2 * ∑ i, q i ^ 2) *
          (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A₀, s, has, hpack⟩ := exists_measure_cubeRestrictBad_le hd hpc
  obtain ⟨ε, hε, t, ht, hMU⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hpq : (1 + ε / 2).HolderConjugate (1 + ε / 2).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  set r := (1 + ε / 2).conjExponent with hr
  set τ : ℕ := ⌈((2 * d - 1 : ℕ) : ℝ) * r⌉₊ with hτ
  have hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ := Nat.le_ceil _
  obtain ⟨Aτ, hAτ, htK⟩ := hpack τ
  obtain ⟨K, hK, hMβ⟩ := htK t ht
  obtain ⟨CM, hCM, hMey⟩ := hMU K hK
  obtain ⟨Cb, hCb, hbad⟩ := hMβ 2 (4 * d + 1)
  obtain ⟨CD, hCD, hdef⟩ := exists_lintegral_cubeMuDefect_le_tau hd hpc
  obtain ⟨Cmj, hCmj, hmaj⟩ := exists_cubeMuRestrictFieldError_majorant hd hpc
  set Λ₀ := restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) with hΛ₀def
  have hΛ₀ : 0 ≤ Λ₀ := restrictOffBadConst_nonneg (Real.rpow_nonneg hAτ _) hCM
  set Ccs : ℝ := ((Cmj * Cb) ^ (1 / 2 : ℝ)).toReal with hCcs
  have hCcs0 : 0 ≤ Ccs := ENNReal.toReal_nonneg
  have hae := (ae_partitionEvent hd hpc).and has
  refine ⟨Λ₀ * CD + Ccs, by positivity, fun n m q g G hg hn hnm hmn => ?_⟩
  set U : TriadicCube d := ⟨m, 0⟩ with hU
  have hUs : U.scale = m := rfl
  obtain ⟨M, hMm, hMle, hM2⟩ := hmaj U n hnm.le q g G hg
  set P := ∑ i, q i ^ 2 with hPdef
  set T := ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)) with hTdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hGP0 : 0 ≤ G ^ 2 * P := mul_nonneg (sq_nonneg G) hP0
  have hT1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ T := by
    rw [three_rpow_neg_div_four_eq]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => cubeTau_nonneg p k)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  have hvol := U.latticeVolume_pos
  set f : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (G ^ 2 * Λ₀ * (cubeMuDefect ω U n q / U.latticeVolume)) with hfdef
  have hgood : ∀ᵐ ω ∂(latticeBondLaw d p), ω ∉ cubeRestrictBad s t K τ Aτ U n →
      ENNReal.ofReal (cubeMuRestrictFieldError ω U n q g) ≤ f ω := by
    filter_upwards [hae] with ω ⟨hP, hs⟩ hω
    exact ENNReal.ofReal_le_ofReal (cubeMuRestrictFieldError_le_of_not_mem_cubeRestrictBad hd0 hpq
      hτr hCM hAτ hMey hP hs hn hnm hω q hg)
  have hsplit := lintegral_le_add_sqrt_measure (latticeBondLaw d p)
    (fun ω => ENNReal.ofReal (cubeMuRestrictFieldError ω U n q g)) f M
    (cubeRestrictBad s t K τ Aτ U n) hMm hgood hMle
  refine hsplit.trans ?_
  have h1 : ∫⁻ ω, f ω ∂(latticeBondLaw d p) ≤ ENNReal.ofReal (Λ₀ * CD * (G ^ 2 * P) * T) := by
    have hpt : ∀ ω, f ω = ENNReal.ofReal (G ^ 2 * Λ₀ / U.latticeVolume) *
        ENNReal.ofReal (cubeMuDefect ω U n q) := fun ω => by
      simp only [hfdef]
      rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (sq_nonneg G) hΛ₀) hvol.le)]
      congr 1
      ring
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (G ^ 2 * Λ₀ / U.latticeVolume) *
          ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω U n q) ∂(latticeBondLaw d p)
        ≤ ENNReal.ofReal (G ^ 2 * Λ₀ / U.latticeVolume) *
            ENNReal.ofReal (U.latticeVolume * (CD * P * T)) :=
          mul_le_mul_of_nonneg_left (hdef n m q hnm.le) zero_le
      _ = ENNReal.ofReal (Λ₀ * CD * (G ^ 2 * P) * T) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (sq_nonneg G) hΛ₀) hvol.le)]
          congr 1
          field_simp
  have h2 : (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
      (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Ccs * (G ^ 2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    refine le_trans ?_ (sqrt_cubeBadTerm_le hCmj hCb hGP0 (by rw [hUs]; exact hmn))
    exact mul_le_mul' (ENNReal.rpow_le_rpow hM2 (by norm_num))
      (ENNReal.rpow_le_rpow (hbad U n hn hnm hmn) (by norm_num))
  calc ∫⁻ ω, f ω ∂(latticeBondLaw d p) + (∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)) ^ (1 / 2 : ℝ) *
        (latticeBondLaw d p) (cubeRestrictBad s t K τ Aτ U n) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Λ₀ * CD * (G ^ 2 * P) * T) +
          ENNReal.ofReal (Ccs * (G ^ 2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (Λ₀ * CD * (G ^ 2 * P) * T +
          Ccs * (G ^ 2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((Λ₀ * CD + Ccs) * (G ^ 2 * P) * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : Ccs * (G ^ 2 * P) * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ Ccs * (G ^ 2 * P) * T :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
        nlinarith

end Rigidity.Percolation
