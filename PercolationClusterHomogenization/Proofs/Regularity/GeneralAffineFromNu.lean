import PercolationClusterHomogenization.Proofs.Regularity.GeneralNuFlatnessAS
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeMuUpperBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeVariations
import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralPoincareZero
import PercolationClusterHomogenization.Proofs.Lattice.Divergence

/-!
# Harmonic approximations of affine functions on the cluster of `ℤᵈ` from the maximizers of `ν`

The maximizers `v(·, □, eᵢ)` of `ν(□, eᵢ)` are harmonic on the interior of the crossing cluster of
`□` and, by Lemma 5.8 of Armstrong and Dario (arXiv:1609.09431v2), their coarsenings are close to
the affine functions `x ↦ xᵢ`. The combination `∑ᵢ qᵢ v(·, □, eᵢ)` minus a constant is then a
harmonic approximation of `q · x` on a ball (`affineApproximation_at_scale`), the input of Step 3 of
Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1) for `k = 1`, in every
dimension:

* `harmonicOnBall_of_cubeHarmonic`: harmonicity on `𝒞 ∩ B_R` from harmonicity on the interior of the
  crossing cluster of a cube containing `𝒞 ∩ B_R` in its interior;
* `cubeForm_cubeNuSolution_le`: the energy of `v(·, V, p)` is at most `(3^d/2) |p|₁² |V|`;
* `sum_sq_extend_sub_anchor_le`: Lemma 3.2 with the sizes of the partition cubes bounded by `Z`;
* `sum_sq_coarsen_combo_le`: the flatness of a combination of the coarsenings;
* `componentBallL2_le_of_sums`: the normalized norm on a ball from sums of squares on a cluster.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Proofs.Multiscale (affineFun finsetMean)
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

theorem extend_apply_of_mem (C : OpenComponent ω) (f : C → ℝ) {x : Vertex d} (hx : x ∈ C.supp) :
    Rigidity.Section3.extend C f x = f ⟨x, hx⟩ := by
  simp [Rigidity.Section3.extend, hx]

/-- **Harmonicity on a ball** from harmonicity on the interior of the crossing cluster of a cube. -/
theorem harmonicOnBall_of_cubeHarmonic {V : TriadicCube d} (C : OpenComponent ω)
    {v : CubeFun ω V} (hv : v ∈ cubeHarmonic ω V) (c : ℝ) {R : ℝ}
    (hin : ∀ x : C, x ∈ componentEuclideanBall C 0 R →
      x.val ∈ crossingClusterVertices ω V ∧ V.IsLatticeInterior x.val) :
    HarmonicOnBall C (fun x => cubeExtend ω V v x.val - c) R := by
  intro x hx _
  obtain ⟨hxV, hint⟩ := hin x hx
  rw [mem_cubeHarmonic] at hv
  have h0 := hv ⟨x.val, hxV⟩ hint
  rw [cubeLaplacianAt_apply] at h0
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C _ x.val x.2, ← Finset.sum_filter]
  have e1 : ∑ y : ↥(crossingClusterVertices ω V), (if (openGraph ω).Adj x.val y.1 then
      v y - v ⟨x.val, hxV⟩ else 0) =
      ∑ y ∈ crossingClusterVertices ω V, (if (openGraph ω).Adj x.val y then
        cubeExtend ω V v y - cubeExtend ω V v x.val else 0) := by
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω V)]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rw [cubeExtend_apply_of_mem _ y.2, cubeExtend_apply_of_mem _ hxV]
    · rfl
  rw [e1, ← Finset.sum_filter] at h0
  have hset : (crossingClusterVertices ω V).filter (fun y => (openGraph ω).Adj x.val y) =
      ((lattice d).neighborFinset x.val).filter (fun y => (openGraph ω).Adj x.val y) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨openGraph_le ω hy, hy⟩
    · rintro ⟨-, hy⟩
      exact ⟨Rigidity.Dirichlet.mem_crossingClusterVertices_of_adj hxV (hint y (openGraph_le ω hy)) hy, hy⟩
  rw [hset] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨-, hxy⟩ := Finset.mem_filter.1 hy
  have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
  rw [extend_apply_of_mem C _ hyC, extend_apply_of_mem C _ x.2]
  ring

theorem cubeNuSolution_mem_cubeHarmonic (hP : PartitionEvent ω) {V : TriadicCube d}
    (hV : PartitionResolved ω V) (p : Fin d → ℝ) : cubeNuSolution ω V p ∈ cubeHarmonic ω V := by
  rw [cubeNuSolution_eq hP hV]
  exact (cubeNuMaximizer_spec V p).1

/-- The energy of the maximizer of `ν(V, p)` is at most `(3^d/2) |p|₁² |V|`. -/
theorem cubeForm_cubeNuSolution_le (hP : PartitionEvent ω) {V : TriadicCube d}
    (hV : PartitionResolved ω V) (p : Fin d → ℝ) :
    cubeForm ω V (cubeNuSolution ω V p) (cubeNuSolution ω V p) ≤
      3 ^ d / 2 * (∑ i, |p i|) ^ 2 * V.latticeVolume := by
  rw [cubeNuSolution_eq hP hV]
  obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) V p
  have h1 := cubeNu_mul_latticeVolume_eq p hv hvar
  have h2 := cubeNu_le (ω := ω) (U := V) p
  have hvol := V.latticeVolume_pos
  have := mul_le_mul_of_nonneg_right h2 hvol.le
  linarith

/-- The constant of Lemma 3.2 for the partition into good cubes. -/
noncomputable def coarseErrorConst (d : ℕ) : ℝ :=
  3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))

/-- **Lemma 3.2 with the sizes of the partition cubes bounded by `Z`**:
`Σ_{C_*(U)} (v - [v]_𝒫)² ≤ K² Z^{2d} B(v, v)`. -/
theorem sum_sq_extend_sub_anchor_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (v : CubeFun ω U) {Z : ℝ}
    (hZ : ∀ x ∈ crossingClusterVertices ω U, (3 : ℝ) ^ (partitionCube ω x).scale ≤ Z) :
    ∑ x ∈ crossingClusterVertices ω U,
        (cubeExtend ω U v x - cubeExtend ω U v (partitionAnchor ω x)) ^ 2 ≤
      coarseErrorConst d ^ 2 * Z ^ (2 * d) * cubeForm ω U v v := by
  set P := partitionCoarseData hd hP U hU with hPdef
  have hreach : ∀ z ∈ crossingClusterVertices ω U, (3 : ℝ) ^ P.reachScale z ≤ Z := by
    intro z hz
    have hne : (P.cluster.filter fun x => z ∈ P.region x).Nonempty :=
      ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ hne fun x => (P.part x).scale
    have hreq : P.reachScale z = (P.part x).scale := hxe
    rw [hreq]
    exact hZ x (Finset.mem_filter.1 hx).1
  have h := partition_sum_abs_sub_coarseAnchor_rpow_le hd hP hU (cubeExtend ω U v) (s := 2)
    (by norm_num)
  have e1 : ∀ x ∈ crossingClusterVertices ω U,
      |cubeExtend ω U v x - cubeExtend ω U v (partitionAnchor ω x)| ^ (2 : ℝ) =
        (cubeExtend ω U v x - cubeExtend ω U v (partitionAnchor ω x)) ^ 2 := fun x _ => by
    rw [Real.rpow_two, sq_abs]
  have e2 : ∀ z ∈ crossingClusterVertices ω U,
      ((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * (d : ℝ)) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) (cubeExtend ω U v) z ^ (2 : ℝ) =
      ((3 : ℝ) ^ P.reachScale z) ^ (2 * d) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) (cubeExtend ω U v) z ^ 2 :=
    fun z _ => by
      rw [show (2 : ℝ) * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
        Real.rpow_two]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Real.rpow_two] at h
  refine h.trans ?_
  change coarseErrorConst d ^ 2 * _ ≤ _
  rw [mul_assoc, ← sum_gradNormIn_sq_eq_cubeForm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hreach z hz) _)
    (sq_nonneg _)

/-- **The flatness of a combination** of the coarsenings, against the affine function of the
combined slope: `Σ_V (Σᵢ qᵢ gᵢ)² ≤ d |V| Σᵢ qᵢ² flatᵢ`. -/
theorem sum_sq_coarsen_combo_le {V : TriadicCube d} (w : Fin d → Vertex d → ℝ)
    (q : Fin d → ℝ) :
    ∑ x ∈ V.toIntegerCube.vertices,
        (∑ i, q i * w i x - affineFun q x -
          ∑ i, q i * finsetMean V.toIntegerCube.vertices
            (fun y => w i y - affineFun (Pi.single i 1) y)) ^ 2 ≤
      d * V.latticeVolume * ∑ i, q i ^ 2 * cubeFlatnessError V (w i) (Pi.single i 1) := by
  set m : Fin d → ℝ := fun i => finsetMean V.toIntegerCube.vertices
    (fun y => w i y - affineFun (Pi.single i 1) y) with hm
  set g : Fin d → Vertex d → ℝ := fun i x => w i x - affineFun (Pi.single i 1) x - m i with hg
  have haff : ∀ x, affineFun q x = ∑ i, q i * affineFun (Pi.single i 1) x := by
    intro x
    simp only [affineFun, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hlin : ∀ x, ∑ i, q i * w i x - affineFun q x - ∑ i, q i * m i = ∑ i, q i * g i x := by
    intro x
    rw [haff x]
    simp only [hg, mul_sub, Finset.sum_sub_distrib]
  have hflat : ∀ i, ∑ x ∈ V.toIntegerCube.vertices, g i x ^ 2 =
      V.latticeVolume * cubeFlatnessError V (w i) (Pi.single i 1) := by
    intro i
    unfold cubeFlatnessError
    rw [← mul_assoc, mul_inv_cancel₀ V.latticeVolume_pos.ne', one_mul]
  calc ∑ x ∈ V.toIntegerCube.vertices, (∑ i, q i * w i x - affineFun q x - ∑ i, q i * m i) ^ 2
      = ∑ x ∈ V.toIntegerCube.vertices, (∑ i, q i * g i x) ^ 2 :=
        Finset.sum_congr rfl fun x _ => by rw [hlin]
    _ ≤ ∑ x ∈ V.toIntegerCube.vertices, (d : ℝ) * ∑ i, (q i * g i x) ^ 2 := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
          (f := fun i => q i * g i x)
        simpa using h
    _ = d * ∑ i, q i ^ 2 * ∑ x ∈ V.toIntegerCube.vertices, g i x ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = d * V.latticeVolume * ∑ i, q i ^ 2 * cubeFlatnessError V (w i) (Pi.single i 1) := by
        simp only [hflat]
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **The normalized norm on the ball** from the sums of squares over a set of vertices containing
the cluster ball. -/
theorem componentBallL2_le_of_sums (C : OpenComponent ω) (w g : Vertex d → ℝ)
    (S : Finset (Vertex d)) (q : Fin d → ℝ) (c : ℝ) {R F G κ' : ℝ} (hκ' : 0 < κ')
    (hin : ∀ x : C, x ∈ componentEuclideanBall C 0 R → x.val ∈ S)
    (hcard : κ' ≤ (componentEuclideanBall C 0 R).card)
    (hF : ∑ x ∈ S, (g x - affineFun q x - c) ^ 2 ≤ F)
    (hG : ∑ x ∈ S, (w x - g x) ^ 2 ≤ G) :
    componentBallL2 C 0 R (fun x => (w x.val - c) - componentSlope C q x) ≤
      Real.sqrt (2 * (F + G) / κ') := by
  unfold componentBallL2
  apply Real.sqrt_le_sqrt
  have hn : (0 : ℝ) < (componentEuclideanBall C 0 R).card := lt_of_lt_of_le hκ' hcard
  rw [div_le_div_iff₀ hn hκ']
  have hpt : ∀ x : ℝ, ∀ y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith [sq_nonneg (x - y)]
  have hsum : ∑ x ∈ componentEuclideanBall C 0 R,
      ((w x.val - c) - componentSlope C q x) ^ 2 ≤ 2 * (F + G) := by
    calc ∑ x ∈ componentEuclideanBall C 0 R, ((w x.val - c) - componentSlope C q x) ^ 2
        = ∑ z ∈ (componentEuclideanBall C 0 R).map (Function.Embedding.subtype _),
            ((w z - g z) + (g z - affineFun q z - c)) ^ 2 := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Function.Embedding.coe_subtype, componentSlope, affineFun]
          ring
      _ ≤ ∑ z ∈ (componentEuclideanBall C 0 R).map (Function.Embedding.subtype _),
            (2 * (w z - g z) ^ 2 + 2 * (g z - affineFun q z - c) ^ 2) :=
          Finset.sum_le_sum fun z _ => hpt _ _
      _ ≤ ∑ z ∈ S, (2 * (w z - g z) ^ 2 + 2 * (g z - affineFun q z - c) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun _ _ _ => by positivity
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hz
          exact hin x hx
      _ = 2 * ∑ z ∈ S, (w z - g z) ^ 2 + 2 * ∑ z ∈ S, (g z - affineFun q z - c) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (F + G) := by linarith
  have hF0 : 0 ≤ F := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) hF
  have hG0 : 0 ≤ G := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) hG
  exact mul_le_mul hsum hcard hκ'.le (by positivity)

end Rigidity.Proofs.Regularity.GeneralDim
