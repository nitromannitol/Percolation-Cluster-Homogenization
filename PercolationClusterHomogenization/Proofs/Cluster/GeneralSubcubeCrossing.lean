import PercolationClusterHomogenization.Proofs.Cluster.GeneralCoarseEnergyMoments
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSolenoidalField
import PercolationClusterHomogenization.Proofs.Dirichlet.CubeStokes

/-!
# Pairings on a cube and on its subcubes, in every dimension

Step 2 of the proof of Lemma 5.7 of Armstrong and Dario (display (5.29)), in every dimension
`d ≥ 2`. For a triadic cube `U`, a scale `n ≤ scale U`, a field `g` with `|g| ≤ G` and a function
`f`, the pairing `⟨∇f, g⟩_U` over the lattice edges of `U` differs from the sum of the pairings over
the subcubes of scale `n` by the pairing over the edges joining two different subcubes. Such an
edge `(x, x + eᵢ)` starts on the upper face in the direction `i` of the subcube of `x`, so there are
at most `d |U| / 3ⁿ` of them (`card_filter_add_unit_not_mem_triadicCubeAt_le`), and by the
Cauchy–Schwarz inequality
`(⟨∇f, g⟩_U - ∑_V ⟨∇f, g⟩_V)² ≤ G² d (|U| / 3ⁿ) · 2 ∑_{x ∈ U} |∇f|²(x)`
(`latticeEdgePairing_sub_sum_subcubesAt_sq_le`).

For the minimizers of `μ`, the energy of the coarsening is controlled in expectation: for every
`a ≥ 1`, `E[∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x)] ≤ C |q|² |V|^{1 + 1/a}`
(`exists_lintegral_coarse_cubeMuMinimizer_le`, display (4.24) of Armstrong and Dario in expectation,
with the loss `|V|^{1/a}` in place of their `3^{δ n}`). Pointwise the energy is at most
`K² M B(u, u)` with `M ≥ size(□_𝒫)^{2d-1}` on `U` (Lemma 3.3), and `B(u, u) = -2|U| μ(U, q)` is at
most `2 d² K² |q|² ∑_U size^{2d-1} ≤ 2 d² K² |q|² |U| M` (Lemma 4.4); with
`M = X^{1/(2a)}`, `X = ∑_U size^{2a(2d-1)}`, Jensen's inequality for the concave power `1/a` and the
moments of the partition sizes give the bound. Together these give the expectation of the square of
the crossing term (`exists_lintegral_latticeEdgePairing_sub_sum_subcubesAt_le`). The
two-dimensional versions are `Rigidity.Percolation.edgePairing_sub_sum_subcubes_sq_le` and
`Rigidity.Proofs.Cluster.exists_lintegral_edgePairing_sub_sum_subcubes_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- A vertex of an integer cube whose neighbour in the direction `i` lies outside the cube is on
the upper face in that direction. -/
theorem mem_upperFace_of_add_unit_not_mem {Q : IntegerCube d} {x : Vertex d} {i : Fin d}
    (hx : x ∈ Q.vertices) (hxi : x + unit i ∉ Q.vertices) : x ∈ Q.upperFace i := by
  rw [IntegerCube.mem_upperFace]
  refine ⟨hx, ?_⟩
  rw [IntegerCube.mem_vertices] at hx hxi
  by_contra hne
  apply hxi
  intro j
  have hj := hx j
  change Q.corner j ≤ x j + (unit i : Vertex d) j ∧ x j + (unit i : Vertex d) j <
    Q.corner j + (Q.size : ℤ)
  by_cases hji : j = i
  · subst hji
    rw [unit_apply_self]
    omega
  · rw [unit_apply_ne hji, add_zero]
    exact hj

/-- **The edges leaving the subcubes in one direction.** The vertices `x` of `U` whose neighbour
`x + eᵢ` is not in the subcube of scale `n` of `x` are at most `|U| / 3ⁿ`. -/
theorem card_filter_add_unit_not_mem_triadicCubeAt_le {U : TriadicCube d} {n : ℕ}
    (hn : n ≤ U.scale) (i : Fin d) :
    ((U.toIntegerCube.vertices.filter fun x =>
        x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices).card : ℝ) ≤
      U.latticeVolume / 3 ^ n := by
  have hd : 0 < d := i.pos
  have h := sum_triadicCubeAt_eq hn
    (fun V x => if x + unit i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0)
  have hcard : ((U.toIntegerCube.vertices.filter fun x =>
      x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices).card : ℝ) =
      ∑ x ∈ U.toIntegerCube.vertices,
        if x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard, h]
  have hface : ∀ V ∈ U.subcubesAt n, (∑ x ∈ V.toIntegerCube.vertices,
      if x + unit i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0) ≤ ((3 : ℝ) ^ n) ^ (d - 1) := by
    intro V hV
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : V.toIntegerCube.vertices.filter (fun x => x + unit i ∉ V.toIntegerCube.vertices) ⊆
        V.toIntegerCube.upperFace i := fun x hx => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact mem_upperFace_of_add_unit_not_mem h1 h2
    have h1 := (Finset.card_le_card hsub).trans (Rigidity.Dirichlet.card_upperFace_le V.toIntegerCube i)
    have h2 : (V.toIntegerCube.size : ℝ) = (3 : ℝ) ^ n := by
      change ((3 ^ V.scale : ℕ) : ℝ) = _
      rw [TriadicCube.scale_of_mem_subcubesAt hV]
      push_cast
      rfl
    calc ((V.toIntegerCube.vertices.filter
          fun x => x + unit i ∉ V.toIntegerCube.vertices).card : ℝ)
        ≤ ((V.toIntegerCube.size ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((3 : ℝ) ^ n) ^ (d - 1) := by push_cast; rw [h2]
  refine (Finset.sum_le_sum hface).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ← card_subcubesAt_mul_general U hn]
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hd1 : ((3 : ℝ) ^ n) ^ d = ((3 : ℝ) ^ n) ^ (d - 1) * 3 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hd1]
  field_simp

/-- **Pairings on a cube and on its subcubes** (Armstrong and Dario, proof of Lemma 5.7, Step 2,
deterministic part, every dimension). -/
theorem latticeEdgePairing_sub_sum_subcubesAt_sq_le {U : TriadicCube d} {n : ℕ}
    (hn : n ≤ U.scale) {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G)
    (f : Vertex d → ℝ) :
    (latticeEdgePairing U.toIntegerCube.vertices g f -
        ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g f) ^ 2 ≤
      G ^ 2 * (d * (U.latticeVolume / 3 ^ n)) *
        (2 * ∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices f x ^ 2) := by
  set W := U.toIntegerCube.vertices with hW
  set c : Vertex d → Fin d → Prop := fun x i =>
    x + unit i ∈ W ∧ x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices with hc
  have hsub : ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g f =
      ∑ x ∈ W, ∑ i : Fin d, if x + unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices then
        g x i * (f (x + unit i) - f x) else 0 := by
    rw [hW, sum_triadicCubeAt_eq hn (fun V x => ∑ i : Fin d,
      if x + unit i ∈ V.toIntegerCube.vertices then g x i * (f (x + unit i) - f x) else 0)]
    rfl
  have hdiff : latticeEdgePairing W g f -
      ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g f =
      ∑ x ∈ W, ∑ i : Fin d, if c x i then g x i * (f (x + unit i) - f x) else 0 := by
    rw [hsub, latticeEdgePairing, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h2 : x + unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices
    · have h1 : x + unit i ∈ W := by
        rw [hW, TriadicCube.mem_toIntegerCube_vertices] at hx ⊢
        rw [TriadicCube.mem_toIntegerCube_vertices] at h2
        exact triadicCubeAt_subset hn hx h2
      have hnc : ¬ c x i := fun h => h.2 h2
      rw [if_pos h1, if_pos h2, if_neg hnc, sub_self]
    · by_cases h1 : x + unit i ∈ W
      · rw [if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩, sub_zero]
      · rw [if_neg h1, if_neg h2, if_neg fun h => h1 h.1, sub_zero]
  set a : Vertex d × Fin d → ℝ := fun k => if c k.1 k.2 then g k.1 k.2 else 0 with ha
  set b : Vertex d × Fin d → ℝ := fun k =>
    if c k.1 k.2 then f (k.1 + unit k.2) - f k.1 else 0 with hb
  have h1 : (∑ x ∈ W, ∑ i : Fin d, if c x i then g x i * (f (x + unit i) - f x) else 0) =
      ∑ k ∈ W ×ˢ (Finset.univ : Finset (Fin d)), a k * b k := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, hb]
    split_ifs <;> simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (W ×ˢ (Finset.univ : Finset (Fin d))) a b
  have ha2 : ∑ k ∈ W ×ˢ (Finset.univ : Finset (Fin d)), a k ^ 2 ≤
      G ^ 2 * (d * (U.latticeVolume / 3 ^ n)) := by
    rw [Finset.sum_product, Finset.sum_comm]
    have hterm : ∀ i : Fin d, ∑ x ∈ W, a (x, i) ^ 2 ≤ G ^ 2 * (U.latticeVolume / 3 ^ n) := by
      intro i
      calc ∑ x ∈ W, a (x, i) ^ 2
          ≤ ∑ x ∈ W, G ^ 2 * (if x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices then
              (1 : ℝ) else 0) := by
            refine Finset.sum_le_sum fun x _ => ?_
            simp only [ha]
            by_cases hcx : c x i
            · rw [if_pos hcx, if_pos hcx.2, mul_one, ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hg x i) 2
            · rw [if_neg hcx, zero_pow two_ne_zero]
              split_ifs <;> positivity
        _ = G ^ 2 * ((W.filter fun x =>
              x + unit i ∉ (triadicCubeAt n x).toIntegerCube.vertices).card : ℝ) := by
            rw [← Finset.mul_sum, Finset.card_filter]
            push_cast
            rfl
        _ ≤ G ^ 2 * (U.latticeVolume / 3 ^ n) :=
            mul_le_mul_of_nonneg_left (card_filter_add_unit_not_mem_triadicCubeAt_le hn i)
              (sq_nonneg _)
    calc ∑ i : Fin d, ∑ x ∈ W, a (x, i) ^ 2
        ≤ ∑ _i : Fin d, G ^ 2 * (U.latticeVolume / 3 ^ n) := Finset.sum_le_sum fun i _ => hterm i
      _ = G ^ 2 * (d * (U.latticeVolume / 3 ^ n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hb2 : ∑ k ∈ W ×ˢ (Finset.univ : Finset (Fin d)), b k ^ 2 ≤ latticeEdgeEnergy W f := by
    rw [latticeEdgeEnergy, Finset.sum_product]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
    simp only [hb]
    by_cases hcx : c x i
    · rw [if_pos hcx, if_pos hcx.1]
    · rw [if_neg hcx, zero_pow two_ne_zero]
      split_ifs <;> positivity
  have hE := latticeEdgeEnergy_le_two_mul_sum_gradNormIn_sq W f
  rw [hdiff, h1]
  refine hcs.trans ?_
  have hGd : 0 ≤ G ^ 2 * (d * (U.latticeVolume / 3 ^ n)) := by
    have := U.latticeVolume_pos
    positivity
  calc (∑ k ∈ W ×ˢ (Finset.univ : Finset (Fin d)), a k ^ 2) *
        ∑ k ∈ W ×ˢ (Finset.univ : Finset (Fin d)), b k ^ 2
      ≤ (G ^ 2 * (d * (U.latticeVolume / 3 ^ n))) * latticeEdgeEnergy W f :=
        mul_le_mul ha2 hb2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hGd
    _ ≤ _ := mul_le_mul_of_nonneg_left hE hGd

/-- **The Dirichlet energy of the minimizer of `μ` by the partition sizes**:
`B(u, u) ≤ 2 d² K² |q|² ∑_U size^{2d-1}`. -/
theorem cubeForm_cubeMuMinimizer_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q) ≤
      2 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
        partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) := by
  obtain ⟨hu, hvar⟩ := cubeMuMinimizer_spec hd hP hU q
  have hμ := cubeMu_eq_of_forall_cubeForm_eq hd hP hU hu hvar
  have hneg := neg_cubeMu_le_cubeMuBound_mul hd hP hU q
  have hvol := U.latticeVolume_pos
  have hΛ : cubeMuBound ω U * U.latticeVolume ≤
      d * d * coarseGradConstant d ^ 2 *
        partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) := by
    rw [cubeMuBound, div_mul_cancel₀ _ hvol.ne']
    exact mul_le_mul_of_nonneg_left (partitionSizeSum_le_succ hP _ hd) (by positivity)
  rw [hμ] at hneg
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have h1 : cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q) ≤
      2 * (cubeMuBound ω U * U.latticeVolume) * ∑ i, q i ^ 2 := by
    rw [neg_div, neg_neg, div_le_iff₀ hvol] at hneg
    nlinarith
  calc cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q)
      ≤ 2 * (cubeMuBound ω U * U.latticeVolume) * ∑ i, q i ^ 2 := h1
    _ ≤ 2 * (d * d * coarseGradConstant d ^ 2 *
        partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1)) * ∑ i, q i ^ 2 := by gcongr
    _ = _ := by ring

/-- The sum of the `(2d-1)`-th powers of the sizes is at most `|S| X^{1/(2a)}`,
`X = ∑_S size^{(2d-1) 2a}`. -/
theorem partitionSizeSum_le_card_mul_rpow (S : Finset (Vertex d)) {a : ℕ} (ha : 1 ≤ a) :
    partitionSizeSum ω S (2 * d - 1) ≤
      S.card * partitionSizeSum ω S ((2 * d - 1) * (2 * a)) ^ (1 / ((2 * a : ℕ) : ℝ)) := by
  have hsz : ∀ z, 0 ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) :=
    fun z => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _
  have hterm : ∀ z ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) ≤
      partitionSizeSum ω S ((2 * d - 1) * (2 * a)) ^ (1 / ((2 * a : ℕ) : ℝ)) := by
    intro z hz
    have h := le_rpow_sum_pow (s := S) hsz (a := 2 * a) (by omega) hz
    refine h.trans (le_of_eq ?_)
    unfold partitionSizeSum
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← pow_mul]
  unfold partitionSizeSum at hterm ⊢
  calc ∑ z ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1)
      ≤ ∑ _z ∈ S, (∑ z ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^
          ((2 * d - 1) * (2 * a))) ^ (1 / ((2 * a : ℕ) : ℝ)) := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The energy of the coarsened minimizer of `μ`, pointwise**:
`∑_U |∇[u]_𝒫|² ≤ 2 d² K⁴ |q|² |U| X^{1/a}`, `X = ∑_U size^{(2d-1) 2a}`. -/
theorem sum_gradNormIn_coarse_cubeMuMinimizer_le_rpow (hd : 0 < d) (hP : PartitionEvent ω)
    (U : TriadicCube d) (q : Fin d → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    ∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2 ≤
      2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 * (∑ i, q i ^ 2) *
        U.latticeVolume *
          partitionSizeSum ω U.toIntegerCube.vertices ((2 * d - 1) * (2 * a)) ^ (1 / (a : ℝ)) := by
  set X := partitionSizeSum ω U.toIntegerCube.vertices ((2 * d - 1) * (2 * a)) with hX
  have hX0 : 0 ≤ X := partitionSizeSum_nonneg _ _
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hR0 : 0 ≤ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 *
      (∑ i, q i ^ 2) * U.latticeVolume * X ^ (1 / (a : ℝ)) := by
    have := U.latticeVolume_pos
    have := Real.rpow_nonneg hX0 (1 / (a : ℝ))
    positivity
  by_cases hU : PartitionResolved ω U
  · have hM := sum_gradNormIn_coarse_sq_le_rpow hd hP hU (cubeMuMinimizer ω U q)
      (a := 2 * a) (by omega)
    have hB := cubeForm_cubeMuMinimizer_le hd hP hU q
    have hS := partitionSizeSum_le_card_mul_rpow (ω := ω) U.toIntegerCube.vertices ha
    rw [← hX] at hM hS
    have hcard : (U.toIntegerCube.vertices.card : ℝ) = U.latticeVolume :=
      U.card_toIntegerCube_vertices
    rw [hcard] at hS
    have hr : X ^ (1 / ((2 * a : ℕ) : ℝ)) * X ^ (1 / ((2 * a : ℕ) : ℝ)) = X ^ (1 / (a : ℝ)) := by
      rw [← Real.rpow_add' hX0]
      · congr 1
        have : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
        push_cast
        field_simp
        ring
      · have : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
        positivity
    have hXr := Real.rpow_nonneg hX0 (1 / ((2 * a : ℕ) : ℝ))
    have hB0 := cubeForm_self_nonneg (ω := ω) (cubeMuMinimizer ω U q)
    refine hM.trans ?_
    calc coarseGradConstant d ^ 2 * (X ^ (1 / ((2 * a : ℕ) : ℝ)) *
          cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q))
        ≤ coarseGradConstant d ^ 2 * (X ^ (1 / ((2 * a : ℕ) : ℝ)) *
          (2 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
            (U.latticeVolume * X ^ (1 / ((2 * a : ℕ) : ℝ))))) := by
          gcongr
          exact hB.trans (mul_le_mul_of_nonneg_left hS (by positivity))
      _ = 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 * (∑ i, q i ^ 2) *
          U.latticeVolume * (X ^ (1 / ((2 * a : ℕ) : ℝ)) * X ^ (1 / ((2 * a : ℕ) : ℝ))) := by
          ring
      _ = _ := by rw [hr]
  · have h0 : cubeMuMinimizer ω U q = 0 := by
      rw [cubeMuMinimizer, dif_neg fun h => hU h.2.2]
    rw [h0]
    simp only [map_zero, Pi.zero_apply]
    have hz : ∀ x, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun _ => (0 : ℝ)) x ^ 2 = 0 := fun x => by simp [gradNormIn]
    simp only [hz, Finset.sum_const_zero]
    exact hR0

/-- **The expected energy of the coarsened minimizers of `μ`** (Armstrong and Dario, display
(4.24), in expectation, every dimension `d ≥ 2`): for every `a ≥ 1`,
`E[∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x)] ≤ C |q|² |V| |V|^{1/a}`. -/
theorem exists_lintegral_coarse_cubeMuMinimizer_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {a : ℕ} (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube d) (q : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * V.latticeVolume *
          V.latticeVolume ^ (1 / (a : ℝ))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set τ : ℕ := (2 * d - 1) * (2 * a) with hτ
  set Cτ : ℝ := 2 * (τ.factorial : ℝ) * θ ^ τ with hCτ
  have hCτ0 : 0 ≤ Cτ := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  set K : ℝ := 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * Cτ ^ (1 / (a : ℝ)), by positivity, fun V q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set P : ℝ := ∑ i, q i ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hvol := V.latticeVolume_pos
  set X : Configuration d → ℝ := fun ω =>
    partitionSizeSum ω V.toIntegerCube.vertices τ with hXdef
  have hXm : Measurable X := measurable_partitionSizeSum _ _
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => partitionSizeSum_nonneg _ _
  have hpoint : ∀ᵐ ω ∂μ, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2) ≤
      ENNReal.ofReal (K * P * V.latticeVolume) * ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (sum_gradNormIn_coarse_cubeMuMinimizer_le_rpow hd0 hPω V q ha).trans (le_of_eq ?_)
    rw [hK]
  have hEX : ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ ≤ ENNReal.ofReal (Cτ * V.latticeVolume) := by
    have hint := (hmom τ V.toIntegerCube.vertices).1
    have hint2 := (hmom τ V.toIntegerCube.vertices).2
    calc ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ENNReal.ofReal (∫ ω, X ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (f := X) hint (ae_of_all _ hX0)).symm
      _ ≤ ENNReal.ofReal (Cτ * V.latticeVolume) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← V.card_toIntegerCube_vertices]
          exact hint2
  have hJ := lintegral_ofReal_rpow_le μ hXm hX0 (r := 1 / (a : ℝ)) (by positivity)
    (by rw [div_le_one ha0]; exact_mod_cast ha)
  calc ∫⁻ ω, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (K * P * V.latticeVolume) *
          ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (K * P * V.latticeVolume) *
          ∫⁻ ω, ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) ∂μ :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hXm.pow_const _))
    _ ≤ ENNReal.ofReal (K * P * V.latticeVolume) *
          ENNReal.ofReal (Cτ * V.latticeVolume) ^ (1 / (a : ℝ)) := by
        gcongr
        exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
    _ = ENNReal.ofReal (K * Cτ ^ (1 / (a : ℝ)) * P * V.latticeVolume *
          V.latticeVolume ^ (1 / (a : ℝ))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hCτ0 hvol.le]
        congr 1
        ring

/-- **Pairings on a cube and on its subcubes, in expectation** (Armstrong and Dario, proof of
Lemma 5.7, Step 2, every dimension `d ≥ 2`): for a field `g` with `|g| ≤ G` and every `a ≥ 1`,
`E[(⟨∇[u(·, U, q)]_𝒫, g⟩_U - ∑_V ⟨∇[u(·, U, q)]_𝒫, g⟩_V)²] ≤
  C G² |q|² (|U| / 3ⁿ) |U| |U|^{1/a}`. -/
theorem exists_lintegral_latticeEdgePairing_sub_sum_subcubesAt_le [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) {a : ℕ} (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale → ∀ (q : Fin d → ℝ)
      (g : Vertex d → Fin d → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∫⁻ ω, ENNReal.ofReal ((latticeEdgePairing U.toIntegerCube.vertices g
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) -
          ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x))) ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * G ^ 2 * (∑ i, q i ^ 2) * (U.latticeVolume / 3 ^ n) *
          U.latticeVolume * U.latticeVolume ^ (1 / (a : ℝ))) := by
  obtain ⟨C, hC, hE⟩ := exists_lintegral_coarse_cubeMuMinimizer_le hd hpc ha
  refine ⟨2 * d * C, by positivity, fun U n hn q g G hg => ?_⟩
  set μ := latticeBondLaw d p with hμ
  have hv : 0 ≤ U.latticeVolume / 3 ^ n := div_nonneg U.latticeVolume_pos.le (by positivity)
  have hpoint : ∀ ω : Configuration d, ENNReal.ofReal ((latticeEdgePairing U.toIntegerCube.vertices
        g (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) -
      ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x))) ^ 2) ≤
      ENNReal.ofReal (2 * d * G ^ 2 * (U.latticeVolume / 3 ^ n)) *
        ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((latticeEdgePairing_sub_sum_subcubesAt_sq_le hn hg _).trans
      (le_of_eq ?_))
    ring
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (2 * d * G ^ 2 * (U.latticeVolume / 3 ^ n)) *
        ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2) ∂μ :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * d * G ^ 2 * (U.latticeVolume / 3 ^ n)) *
        ∫⁻ ω, ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * d * G ^ 2 * (U.latticeVolume / 3 ^ n)) *
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * U.latticeVolume *
          U.latticeVolume ^ (1 / (a : ℝ))) := by
        gcongr
        exact hE U q
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Rigidity.Percolation
