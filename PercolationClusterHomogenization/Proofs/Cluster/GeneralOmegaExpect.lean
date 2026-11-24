import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaMeasurable
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSIUpgrade
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRhoSubadditive
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubaddTail

/-!
# The pointwise chain of the proof of Lemma 5.9 on the event of small partition cubes

On the event `PartitionSizeLe ω □_{n+1} ℓ` that the partition exists and the partition cubes of
the vertices of `□_{n+1}` have scale at most `ℓ ≤ n`, the error terms of the pointwise chain of the
proof of Lemma 5.9 of Armstrong and Dario are bounded deterministically:

* the boundary error of the maximizer of `ν(□_n, p)` by `|p|₁ Yc(ℓ) 3^{-n/2}`
  (`cubeComparisonError_le_of_sizeLe`);
* the coarsening error `∑_{C_*(U)} |w - [w]_𝒫|²` by `K² 9^{dℓ} B(w, w)` (Lemma 3.2 with `s = 2`,
  `cubeCoarseningError_le_of_sizeLe`), with `B(w, w) ≤ 2 B(v_U) + 2 B(u_U)` bounded through
  `ν ≤ (3^d/4) |p|₁²` and Lemma 4.4;
* the energy of the differences of the maximizers of `ν` by the subadditivity of `ν`
  (`cubeNuDefect_add_le`), with the exceptional count bounded by the indicators of
  `ExceptionalMajorant`.

This gives `ω(□_n) ≤ c₀ + 3 (M_ν + D^μ_n)/|□_n| + K_n 4 |□_{n+1}| (F_v + F_u)`
(`cubeOmegaChain_le_of_sizeLe`), with a deterministic `c₀`, the majorant `M_ν` of `D^ν_n`, which is
measurable, and the measurable flatness errors `F_u`, `F_v`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The constant of Lemma 3.2 with `s = 2`. -/
noncomputable def coarseningConst (d : ℕ) : ℝ :=
  3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))

theorem coarseningConst_nonneg (d : ℕ) : 0 ≤ coarseningConst d := by
  unfold coarseningConst
  positivity

theorem gradNormIn_sq_eq_clusterGradSq (S : Finset (Vertex d)) (f : Vertex d → ℝ) (z : Vertex d) :
    gradNormIn (openGraph ω) S f z ^ 2 = clusterGradSq ω S f z := by
  unfold gradNormIn clusterGradSq
  rw [Real.sq_sqrt (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun y _ => ite_nonneg (sq_nonneg _) le_rfl))]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact and_comm

/-- **The coarsening error on the event of small partition cubes** (Lemma 3.2 with `s = 2`). -/
theorem cubeCoarseningError_le_of_sizeLe (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {ℓ : ℕ}
    (hS : ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ ℓ) (w : CubeFun ω U) :
    cubeCoarseningError ω U w ≤
      coarseningConst d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * d) * cubeForm ω U w w := by
  have h := partition_sum_abs_sub_coarseAnchor_rpow_le hd hP hU (cubeExtend ω U w)
    (s := 2) one_le_two
  set P := partitionCoarseData hd hP U hU with hPdef
  have hρ : ∀ z, P.reachScale z ≤ ℓ := by
    intro z
    unfold CoarseData.reachScale
    refine Finset.sup_le fun x hx => ?_
    have hxC : x ∈ crossingClusterVertices ω U := (Finset.mem_filter.1 hx).1
    exact hS x ((U.mem_toIntegerCube_vertices x).1 (Finset.filter_subset _ _ hxC))
  have hpt : ∀ z ∈ crossingClusterVertices ω U,
      ((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * (d : ℝ)) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) (cubeExtend ω U w) z ^ (2 : ℝ) ≤
      ((3 : ℝ) ^ ℓ) ^ (2 * d) *
        clusterGradSq ω (crossingClusterVertices ω U) (cubeExtend ω U w) z := by
    intro z _
    rw [Real.rpow_two, gradNormIn_sq_eq_clusterGradSq,
      show (2 : ℝ) * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (hρ z)) _
    · unfold clusterGradSq
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlhs : cubeCoarseningError ω U w = ∑ x ∈ crossingClusterVertices ω U,
      |cubeExtend ω U w x - cubeExtend ω U w (partitionAnchor ω x)| ^ (2 : ℝ) := by
    unfold cubeCoarseningError
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.rpow_two, sq_abs]
  rw [hlhs]
  refine h.trans ?_
  rw [Real.rpow_two]
  calc coarseningConst d ^ 2 * ∑ z ∈ crossingClusterVertices ω U,
        ((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * (d : ℝ)) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω U) (cubeExtend ω U w) z ^ (2 : ℝ)
      ≤ coarseningConst d ^ 2 * ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ ℓ) ^ (2 * d) *
          clusterGradSq ω (crossingClusterVertices ω U) (cubeExtend ω U w) z :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (sq_nonneg _)
    _ = coarseningConst d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * d) * cubeForm ω U w w := by
        rw [← Finset.mul_sum, sum_clusterGradSq_eq_cubeForm]
        ring

/-- `B(a - b) ≤ 2 B(a) + 2 B(b)`. -/
theorem cubeForm_sub_le {U : TriadicCube d} (a b : CubeFun ω U) :
    cubeForm ω U (a - b) (a - b) ≤ 2 * cubeForm ω U a a + 2 * cubeForm ω U b b := by
  have h := cubeForm_self_nonneg (ω := ω) (a + b)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h ⊢
  rw [cubeForm_symm b a] at h ⊢
  linarith

/-- **The comparison constant grows like `(3^ℓ)^d`.** -/
theorem comparisonCap_le (hd : 0 < d) (ℓ : ℕ) :
    comparisonCap d ℓ ≤ (1 + 2 * d + 2 * 3 ^ d * (d * √(4 * Real.exp 1))) * ((3 : ℝ) ^ ℓ) ^ d := by
  unfold comparisonCap
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  have hwd : w ≤ w ^ d := le_self_pow₀ hw1 hd.ne'
  have h1 : (1 : ℝ) ≤ w ^ d := one_le_pow₀ hw1
  have hsq : √(d * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1)))))) ≤
      d * √(4 * Real.exp 1) * w ^ d := by
    have hin : d * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1))))) ≤
        (d * √(4 * Real.exp 1) * w ^ d) ^ 2 := by
      have hw2 : w + 1 ≤ 2 * w := by linarith
      have key : ∀ x : ℝ, x ^ (2 * (d - 1)) * x ^ 2 = (x ^ d) ^ 2 := fun x => by
        rw [← pow_add, ← pow_mul, show 2 * (d - 1) + 2 = d * 2 by omega]
      have hpow : w ^ (2 * (d - 1)) * w ^ 2 = (w ^ d) ^ 2 := key w
      have hww : w ^ (2 * (d - 1)) * w ≤ w ^ (2 * (d - 1)) * w ^ 2 := by
        have : w ≤ w ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have he := Real.exp_pos 1
      calc (d : ℝ) * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1)))))
          ≤ d * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (2 * w))))) := by gcongr
        _ = d ^ 2 * (4 * Real.exp 1) * (w ^ (2 * (d - 1)) * w) := by ring
        _ ≤ d ^ 2 * (4 * Real.exp 1) * (w ^ (2 * (d - 1)) * w ^ 2) := by gcongr
        _ = (d : ℝ) ^ 2 * (4 * Real.exp 1) * (w ^ d) ^ 2 := by rw [hpow]
    calc _ ≤ √((d * √(4 * Real.exp 1) * w ^ d) ^ 2) := Real.sqrt_le_sqrt hin
      _ = d * √(4 * Real.exp 1) * w ^ d := Real.sqrt_sq (by positivity)
  have h3 : (0 : ℝ) ≤ 2 * 3 ^ d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq h3, mul_le_mul_of_nonneg_left hwd
    (by positivity : (0 : ℝ) ≤ 2 * d)]

end Rigidity.Percolation
