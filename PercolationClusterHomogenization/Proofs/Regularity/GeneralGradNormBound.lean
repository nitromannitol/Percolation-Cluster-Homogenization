import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseBoundAS
import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralDatumBounds

/-!
# The gradient norm of Theorem 1 on triadic cubes from the Meyers estimate

For `u` harmonic on the infinite cluster, the normalized `L^{2q}` norm `cubeGradNorm ω (j + 1) (2q)`
of the open gradient of `u` on `C_*(□_{j+1})`, the quantity `M` of Theorem 1 of Armstrong and Dario
(arXiv:1609.09431v2) in every dimension, is bounded by the normalized `L²` norm of `u - c` on
`C_*(□_{j+3})` (`cubeGradNorm_le`):
`M ≤ C_M^{1/(2q)} (8 d 3^d)^{1/2} 3^{-j} |□_{j+3}|^{-1/2} ‖u - c‖_{L²(C_*(□_{j+3}))}`.
The proof combines the Meyers estimate on `□_{j+1}` for `u` on the crossing cluster of `□_{j+3}`
with the Caccioppoli inequality on `C_*(□_{j+3})` from `□_{j+2}`
(`energy_enl_succ_le_caccioppoli_cube`), which uses that the vertices of the infinite cluster in
the inner part of `□_{j+3}` lie in `C_*(□_{j+3})` (`mem_crossingClusterVertices_inner_cube`).
The planar form is `planarGradNormTwo_le`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster Rigidity.Proofs.Cluster.GeneralDim
open Rigidity.Dirichlet
open scoped Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- **The infinite cluster in the inner part of `□_{j+3}`** lies in `C_*(□_{j+3})` when the
partition cubes of `□_{j+3}` have scale at most `j`. -/
theorem mem_crossingClusterVertices_inner_cube (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (hinf : C.supp.Infinite) {j : ℕ}
    (hsc : ∀ x ∈ triadicCubeFinset d (j + 3) 0, (partitionCube ω x).scale ≤ j) {x : Vertex d}
    (hxC : x ∈ C.supp) (hx : ∀ k, 2 * |x k| < 17 * 3 ^ j) :
    x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩ := by
  have h27 : (3 : ℤ) ^ (j + 3) = 27 * 3 ^ j := by ring
  have h0 : (0 : ℤ) < 3 ^ j := by positivity
  have hxsq : x ∈ triadicCubeFinset d (j + 3) 0 := by
    rw [mem_cubeFinset_iff_int]
    intro k
    have := hx k
    rw [h27]; linarith
  have hxU : x ∈ (⟨j + 3, 0⟩ : TriadicCube d).vertices := mem_cubeFinset_iff_vertices.1 hxsq
  have hC : (openGraph ω).connectedComponentMk x = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hxC
  have hxinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := by rw [hC]; exact hinf
  set Q := partitionCube ω x with hQdef
  have hs : Q.scale ≤ j := hsc x hxsq
  have hsub : Q.parent.vertices ∪ cubeAt x (3 ^ Q.scale / 2) ⊆
      (⟨j + 3, 0⟩ : TriadicCube d).vertices := by
    intro y hy
    have hy' := parent_union_cubeAt_subset hP x hy
    rw [mem_triadicCube_zero_iff']
    intro i
    have hyi : |y i - x i| ≤ ((3 ^ (Q.scale + 1) : ℕ) : ℤ) := hy' i
    have hcast : (((3 ^ (Q.scale + 1) : ℕ) : ℤ)) = (3 : ℤ) ^ (Q.scale + 1) := by norm_num
    rw [hcast] at hyi
    have hpow : (3 : ℤ) ^ (Q.scale + 1) ≤ 3 * 3 ^ j := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hs) (by norm_num)
    rw [h27]
    have hxi := hx i
    have ha := abs_sub_abs_le_abs_sub (y i) (x i)
    linarith
  have hreach : (openIn ω (⟨j + 3, 0⟩ : TriadicCube d).vertices).Reachable x
      (partitionAnchor ω x) :=
    reachable_openIn_mono hsub (reachable_partitionAnchor_of_infinite hd hP hxinf)
  obtain ⟨root, hroot, hra⟩ := crossingCluster_partitionCube_subset hd hP hxU
    (show Q.scale ≤ (⟨j + 3, 0⟩ : TriadicCube d).scale from by
      show Q.scale ≤ j + 3
      omega)
    (partitionAnchor_mem_crossingCluster hP x)
  exact mem_crossingClusterVertices.2 ⟨root, hroot, hra.trans hreach.symm⟩

set_option maxHeartbeats 400000 in
/-- **The Caccioppoli step on `C_*(□_{j+3})`**: the energy of `u` on `□_{j+2}`, counted with the
edges inside the crossing cluster of `□_{j+3}`, is at most
`8 d 3^{-2(j+1)} Σ_{C_*(□_{j+3})} (u - c)²`. -/
theorem energy_enl_succ_le_caccioppoli_cube (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h3C : ∀ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, x ∈ C.supp)
    (hin : ∀ x, x ∈ C.supp → (∀ k, 2 * |x k| < 17 * 3 ^ j) →
      x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0) (c : ℝ) :
    ∑ z ∈ enl 1 (j + 1) (0 : Vertex d), clusterEnergy ω (crossingClusterVertices ω ⟨j + 3, 0⟩)
        (Rigidity.Section3.extend C u) z ≤
      8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - c) ^ 2 := by
  set f := Rigidity.Section3.extend C u with hfdef
  set U := crossingClusterVertices ω ⟨j + 3, 0⟩ with hUdef
  set V' := (triadicCubeFinset d (j + 2) 0).filter (· ∈ C.supp) with hV'def
  have h9 : (3 : ℤ) ^ (j + 2) = 9 * 3 ^ j := by ring
  have hV'U : V' ⊆ U := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    refine hin x hx2 fun k => ?_
    have := (mem_cubeFinset_iff_int.1 hx1) k
    have h0 : (0 : ℤ) < 3 ^ j := by positivity
    rw [h9] at this; linarith
  have hE : ∑ z ∈ enl 1 (j + 1) (0 : Vertex d), clusterEnergy ω U f z ≤
      ∑ z ∈ V', clusterGradSq ω U f z := by
    calc ∑ z ∈ enl 1 (j + 1) (0 : Vertex d), clusterEnergy ω U f z
        = ∑ z ∈ (enl 1 (j + 1) (0 : Vertex d)).filter (· ∈ U), clusterGradSq ω U f z := by
          rw [Finset.sum_filter]; rfl
      _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
            fun _ _ _ => clusterGradSq_nonneg _ _ _ _
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          rw [enl_one_zero_eq_cube_succ] at hz1
          exact Finset.mem_filter.2 ⟨mem_cubeFinset_of_mem_cube_zero hz1, h3C z hz2⟩
  have hr : (0 : ℝ) < 3 ^ (j + 1) := by positivity
  have hdist : ∀ x ∈ V', ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) →
      (3 : ℝ) ^ (j + 1) ≤ (supDist x z : ℝ) := by
    rintro x hx z hz ⟨y, hzy, hyU⟩
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp (h3C z hz) hzy
    have hy2 : ¬ ∀ k, 2 * |y k| < 17 * 3 ^ j := fun h => hyU (hin y hyC h)
    push Not at hy2
    obtain ⟨k, hk⟩ := hy2
    have hzk := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hzy) k
    have hxk := (mem_cubeFinset_iff_int.1 hx1) k
    have hle : (x k - z k).natAbs ≤ supDist x z :=
      Finset.le_sup (f := fun i => (x i - z i).natAbs) (Finset.mem_univ k)
    have hcast : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ ((x k - z k).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      have h3 : (3 : ℤ) ^ (j + 1) = 3 * 3 ^ j := by ring
      have hab := abs_sub_abs_le_abs_sub (z k) (x k)
      have hyz := abs_sub_abs_le_abs_sub (y k) (z k)
      rw [abs_sub_comm (z k) (x k)] at hab
      rw [h9] at hxk
      have h1 : (1 : ℤ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
      generalize |x k| = a at hxk hab
      generalize |z k| = b at hab hyz
      generalize |y k| = c at hk hyz
      generalize |x k - z k| = e at hab ⊢
      generalize |y k - z k| = g at hzk hyz
      generalize (3 : ℤ) ^ (j + 1) = t at h3 ⊢
      generalize (3 : ℤ) ^ j = t' at h3 hxk hk h1
      omega
    have : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ (supDist x z : ℤ) := hcast.trans (by exact_mod_cast hle)
    exact_mod_cast this
  have hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) →
      openLaplacian ω (fun y => f y - c) x = 0 := by
    intro x hx _
    have hx2 := h3C x hx
    rw [openLaplacian_sub_const, hfdef, openLaplacian_extend_eq_componentLaplacian C u hx2]
    exact hharm x hx2 (mem_cubeFinset_of_mem_crossingClusterVertices hx)
  have hcac := caccioppoli_cluster ω U V' hV'U hr hdist (fun y => f y - c) hu
  have e1 : ∑ x ∈ V', clusterGradSq ω U (fun y => f y - c) x =
      ∑ x ∈ V', clusterGradSq ω U f x :=
    Finset.sum_congr rfl fun x _ => clusterGradSq_sub_const_eq U f c x
  rw [e1] at hcac
  have hsumU : ∑ x ∈ U.filter (fun x => ¬ (x ∈ V' ∧
      ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V')), (f x - c) ^ 2 ≤
      ∑ x ∈ U, (f x - c) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  calc _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := hE
    _ ≤ _ := hcac
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumU (by positivity)

set_option maxHeartbeats 400000 in
/-- **The gradient norm of Theorem 1 on `C_*(□_{j+1})`** from the Meyers estimate `hM` on
`□_{j+1}` and the Caccioppoli inequality on `C_*(□_{j+3})`:
`M ≤ C_M^{1/(2q)} (8 d 3^d)^{1/2} 3^{-j} ‖u - c‖_{L̲²(C_*(□_{j+3}))}`. -/
theorem cubeGradNorm_le (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h13 : crossingClusterVertices ω ⟨j + 1, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (h3C : ∀ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, x ∈ C.supp)
    (hin : ∀ x, x ∈ C.supp → (∀ k, 2 * |x k| < 17 * 3 ^ j) →
      x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    {q CM : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM)
    (hM : avg (cube (j + 1) (0 : Vertex d)) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω ⟨j + 1 + 2, 0⟩)
          (Rigidity.Section3.extend C u) x ^ q) ≤
      CM * avg (enl 1 (j + 1) (0 : Vertex d))
        (clusterEnergy ω (crossingClusterVertices ω ⟨j + 1 + 2, 0⟩)
          (Rigidity.Section3.extend C u)) ^ q)
    (c : ℝ) :
    cubeGradNorm ω (j + 1) (2 * q) (Rigidity.Section3.extend C u) ≤
      CM ^ (1 / (2 * q)) * √(8 * d * 3 ^ d) / 3 ^ j *
        clusterCubeL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - c) := by
  set f := Rigidity.Section3.extend C u with hfdef
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex d → ℝ,
      E = clusterEnergy ω (crossingClusterVertices ω ⟨j + 3, 0⟩) f := ⟨_, rfl⟩
  have hM' : avg (cube (j + 1) (0 : Vertex d)) (fun x => E x ^ q) ≤
      CM * avg (enl 1 (j + 1) (0 : Vertex d)) E ^ q := by rw [hEdef]; exact hM
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 (j + 1) (0 : Vertex d), E z := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  have hq0 : 0 < q := by linarith
  set N : ℝ := ((3 : ℝ) ^ (j + 1)) ^ d with hNdef
  have hN : (0 : ℝ) < N := by positivity
  have hF : (0 : ℝ) < 3 ^ d := by positivity
  have hcube : ((cube (j + 1) (0 : Vertex d)).card : ℝ) = N := card_cube (j + 1) 0
  have henl : ((enl 1 (j + 1) (0 : Vertex d)).card : ℝ) = 3 ^ d * N := by
    rw [card_enl, hNdef, ← mul_pow, pow_succ' (3 : ℝ) (j + 1)]
  -- the `L^{2q}` sum against the energy
  have hS : ∑ x ∈ crossingClusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (crossingClusterVertices ω ⟨j + 1, 0⟩) f x ^ (2 * q) ≤
      N * (CM * (A / (3 ^ d * N)) ^ q) := by
    calc ∑ x ∈ crossingClusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
          (crossingClusterVertices ω ⟨j + 1, 0⟩) f x ^ (2 * q)
        ≤ ∑ x ∈ crossingClusterVertices ω ⟨j + 1, 0⟩, E x ^ q := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Real.rpow_mul (gradNormIn_nonneg _ _ _ _), Real.rpow_two]
          refine Real.rpow_le_rpow (sq_nonneg _) ?_ hq0.le
          have hz2 := h13 hx
          rw [hEdef, gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num)
            (Finset.sum_nonneg fun y _ => by split_ifs <;> positivity)), clusterEnergy,
            if_pos hz2, clusterGradSq, ← Finset.sum_filter]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
            obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
            exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy2, h13 hy1⟩)
            fun _ _ _ => sq_nonneg _
      _ ≤ ∑ x ∈ cube (j + 1) (0 : Vertex d), E x ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => mem_cube_zero_of_mem_cubeFinset
              (mem_cubeFinset_of_mem_crossingClusterVertices hz))
            fun z _ _ => Real.rpow_nonneg (hE0 z) _
      _ = N * avg (cube (j + 1) (0 : Vertex d)) (fun x => E x ^ q) := by
          rw [avg, hcube]; field_simp
      _ ≤ N * (CM * avg (enl 1 (j + 1) (0 : Vertex d)) E ^ q) :=
          mul_le_mul_of_nonneg_left hM' hN.le
      _ = N * (CM * (A / (3 ^ d * N)) ^ q) := by
          rw [avg, henl, ← hAdef]
  -- the Caccioppoli step
  have hcac := energy_enl_succ_le_caccioppoli_cube C u h3C hin hharm c
  rw [← hfdef, ← hEdef, ← hAdef] at hcac
  obtain ⟨Ssum, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
      (f x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hcac
  have hS0 : 0 ≤ Ssum := by rw [hSdef]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  set B : ℝ := 8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum / (3 ^ d * N) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hAq : A / (3 ^ d * N) ≤ B := div_le_div_of_nonneg_right hcac (by positivity)
  -- the norm
  unfold cubeGradNorm
  have hsum0 : 0 ≤ ∑ x ∈ crossingClusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (crossingClusterVertices ω ⟨j + 1, 0⟩) f x ^ (2 * q) :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _
  have h1 : (∑ x ∈ crossingClusterVertices ω ⟨j + 1, 0⟩, gradNormIn (openGraph ω)
      (crossingClusterVertices ω ⟨j + 1, 0⟩) f x ^ (2 * q)) / N ≤ CM * B ^ q := by
    rw [div_le_iff₀ hN]
    calc _ ≤ N * (CM * (A / (3 ^ d * N)) ^ q) := hS
      _ ≤ N * (CM * B ^ q) := by
          gcongr
      _ = _ := by ring
  have h2 := Real.rpow_le_rpow (div_nonneg hsum0 hN.le) h1
    (by positivity : (0 : ℝ) ≤ 1 / (2 * q))
  refine h2.trans ?_
  rw [Real.mul_rpow hCM (Real.rpow_nonneg hB0 _), ← Real.rpow_mul hB0,
    show q * (1 / (2 * q)) = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow]
  have hcl : clusterCubeL2 ω (j + 3) (fun x => f x - c) =
      √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) := by
    unfold clusterCubeL2; rw [hSdef]
  rw [hcl]
  have e27 : ((3 : ℝ) ^ (j + 3)) ^ d = 9 ^ d * N := by
    rw [hNdef, ← mul_pow, show j + 3 = (j + 1) + 2 by ring, pow_add,
      mul_comm ((3 : ℝ) ^ (j + 1)) (3 ^ 2)]; norm_num
  have e : B = (√(8 * d * 3 ^ d) / 3 ^ j) ^ 2 * (Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) * (1 / 9) := by
    rw [hBdef, e27, div_pow, Real.sq_sqrt (by positivity), pow_succ]
    have h9 : (9 : ℝ) ^ d = 3 ^ d * 3 ^ d := by rw [← mul_pow]; norm_num
    rw [h9]
    field_simp; ring
  have hle : √B ≤ √(8 * d * 3 ^ d) / 3 ^ j * √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) := by
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    have h19 : √(1 / 9 : ℝ) ≤ 1 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hx0 : 0 ≤ √(8 * d * 3 ^ d) / 3 ^ j * √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) := by positivity
    calc √(8 * d * 3 ^ d) / 3 ^ j * √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) * √(1 / 9)
        ≤ √(8 * d * 3 ^ d) / 3 ^ j * √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) * 1 :=
          mul_le_mul_of_nonneg_left h19 hx0
      _ = _ := mul_one _
  calc CM ^ (1 / (2 * q)) * √B
      ≤ CM ^ (1 / (2 * q)) * (√(8 * d * 3 ^ d) / 3 ^ j *
          √(Ssum / ((3 : ℝ) ^ (j + 3)) ^ d)) :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hCM _)
    _ = _ := by ring

end Rigidity.Proofs.Regularity
