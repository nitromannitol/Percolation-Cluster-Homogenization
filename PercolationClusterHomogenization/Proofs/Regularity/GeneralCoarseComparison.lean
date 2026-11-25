import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicApproximationAS
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRegularityScales
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHMeyers
import PercolationClusterHomogenization.Proofs.Cluster.PartitionReachMoments
import PercolationClusterHomogenization.Proofs.Cluster.ReverseHolderPartition
import PercolationClusterHomogenization.Proofs.Lattice.Divergence
import PercolationClusterHomogenization.Proofs.Lattice.ChemicalDistance

/-!
# The comparison (7.8) of a harmonic function with its coarsening on triadic cubes

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Step 3, in every dimension `d`:
for `3^j` above the minimal scale and `u` harmonic on the cluster,
`|□_j|^{-1/2} ‖u - [u]_𝒫‖_{L²(C_*(□_j))} ≤ K 3^{-j} inf_a |□_{j+3}|^{-1/2} ‖u - a‖_{L²(C_*(□_{j+3}))}`.
The proof combines

* Lemma 3.2 for the partition into good cubes, with the reach scales `ρ`
  (`partition_sum_abs_sub_coarseAnchor_rpow_le`):
  `∑_{C_*(□_j)} |u - [u]_𝒫|² ≤ C₃² ∑_{C_*(□_j)} 3^{2dρ} |∇u|²`;
* the Hölder inequality with the exponent `q > 1` of the Meyers estimate and a bound
  `∑ 3^{2dρq'} ≤ K_ρ 3^{dj}` on the moments of the reach scales (`holder_meyers_bound_of_factor`);
* the Meyers estimate on `□_j` for `u` on the crossing cluster of `□_{j+2}`
  (`meyers_rh_uniform` with the cells of the reverse Hölder partition), whose right side is an
  average over `□_{j+1}`;
* the Caccioppoli inequality on `𝒞 ∩ □_{j+2}` (`caccioppoli_cluster`), from `□_{j+1}`
  (`energy_enl_le_caccioppoli_cube`).

`coarseComparison_on_cube` is the outcome at one scale, and `cubeCoarseComparisonAS_holds` checks
its hypotheses almost surely above a minimal scale, from the minimal scales of Proposition 2.4
(`cubeRegularityScales_holds`, `cubeMinimalScales_holds`) and the density of the infinite cluster.
The planar forms are `coarseComparison_on_square` and `planarCoarseComparisonTwo_of_minimalScales`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster Rigidity.Proofs.Cluster.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- The constant of Lemma 3.2 for the partition into good cubes with reach scales. -/
noncomputable def partitionCoarseConst (d : ℕ) : ℝ :=
  3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))

theorem partitionCoarseConst_nonneg (d : ℕ) : 0 ≤ partitionCoarseConst d := by
  unfold partitionCoarseConst; positivity

/-- The open Laplacian of the extension of a function on a component, at a vertex of the
component, is its Laplacian on the component. -/
theorem openLaplacian_extend_eq_componentLaplacian (C : OpenComponent ω) (u : C → ℝ)
    {x : Vertex d} (hx : x ∈ C.supp) :
    openLaplacian ω (Rigidity.Section3.extend C u) x = componentLaplacian C u ⟨x, hx⟩ := by
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C u x hx, ← Finset.sum_filter,
    openLaplacian]
  congr 1
  ext z
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => ⟨openGraph_le ω h, h⟩, fun h => h.2⟩

theorem clusterGradSq_sub_const_eq (U : Finset (Vertex d)) (f : Vertex d → ℝ) (c : ℝ)
    (x : Vertex d) : clusterGradSq ω U (fun y => f y - c) x = clusterGradSq ω U f x := by
  unfold clusterGradSq
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem clusterGradSq_le_of_subset {U U' : Finset (Vertex d)} (hUU' : U ⊆ U') (f : Vertex d → ℝ)
    (x : Vertex d) : clusterGradSq ω U f x ≤ clusterGradSq ω U' f x := by
  unfold clusterGradSq
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1,
      hUU' (Finset.mem_filter.1 hy).2⟩) fun _ _ _ => sq_nonneg _

theorem enl_one_zero_eq_cube_succ (j : ℕ) :
    enl 1 j (0 : Vertex d) = cube (j + 1) (0 : Vertex d) := by
  rw [enl, cube, center_zero_vertex, center_zero_vertex]

theorem mem_cube_zero_of_mem_cubeFinset {m : ℕ} {x : Vertex d}
    (hx : x ∈ triadicCubeFinset d m 0) : x ∈ cube m (0 : Vertex d) :=
  mem_cube_zero_iff.2 (mem_cubeFinset_iff_vertices.1 hx)

theorem mem_cubeFinset_of_mem_cube_zero {m : ℕ} {x : Vertex d}
    (hx : x ∈ cube m (0 : Vertex d)) : x ∈ triadicCubeFinset d m 0 :=
  mem_cubeFinset_iff_vertices.2 (mem_cube_zero_iff.1 hx)

theorem mem_cubeFinset_mono {m m' : ℕ} (h : m ≤ m') {x : Vertex d}
    (hx : x ∈ triadicCubeFinset d m 0) : x ∈ triadicCubeFinset d m' 0 := by
  rw [mem_cubeFinset_iff_int] at hx ⊢
  intro i
  have := hx i
  have h3 : (3 : ℤ) ^ m ≤ 3 ^ m' := pow_le_pow_right₀ (by norm_num) h
  linarith

/-- **The Hölder step.** For `a, b ≥ 0` on `S`, `q > 1` and the conjugate exponent `q'`, the bounds
`∑ b^q ≤ K_B N (A / (F N))^q` and `∑ a^{q'} ≤ K_A N` give `∑ b a ≤ K_B^{1/q} K_A^{1/q'} A / F`. -/
theorem holder_meyers_bound_of_factor {ι : Type*} (S : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) {q KA KB N A F : ℝ} (hq : 1 < q)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hN : 0 < N) (hA : 0 ≤ A) (hF : 0 < F)
    (hbq : ∑ i ∈ S, b i ^ q ≤ KB * N * (A / (F * N)) ^ q)
    (haq : ∑ i ∈ S, a i ^ Real.conjExponent q ≤ KA * N) :
    ∑ i ∈ S, b i * a i ≤ KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) * (A / F) := by
  have hpq := Real.HolderConjugate.conjExponent hq
  have hq0 : 0 < q := by linarith
  have hq'0 : 0 < Real.conjExponent q := hpq.symm.pos
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq hb ha
  have hB0 : 0 ≤ ∑ i ∈ S, b i ^ q := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) _
  have hA0 : 0 ≤ ∑ i ∈ S, a i ^ Real.conjExponent q :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) _
  have hAN : 0 ≤ A / (F * N) := by positivity
  have h1 : (∑ i ∈ S, b i ^ q) ^ (1 / q) ≤ KB ^ (1 / q) * N ^ (1 / q) * (A / (F * N)) := by
    calc (∑ i ∈ S, b i ^ q) ^ (1 / q) ≤ (KB * N * (A / (F * N)) ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow hB0 hbq (by positivity)
      _ = KB ^ (1 / q) * N ^ (1 / q) * (A / (F * N)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hKB hN.le,
            ← Real.rpow_mul hAN, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have h2 : (∑ i ∈ S, a i ^ Real.conjExponent q) ^ (1 / Real.conjExponent q) ≤
      KA ^ (1 / Real.conjExponent q) * N ^ (1 / Real.conjExponent q) := by
    calc (∑ i ∈ S, a i ^ Real.conjExponent q) ^ (1 / Real.conjExponent q)
        ≤ (KA * N) ^ (1 / Real.conjExponent q) := Real.rpow_le_rpow hA0 haq (by positivity)
      _ = KA ^ (1 / Real.conjExponent q) * N ^ (1 / Real.conjExponent q) :=
          Real.mul_rpow hKA hN.le
  have hNN : N ^ (1 / q) * N ^ (1 / Real.conjExponent q) = N := by
    rw [← Real.rpow_add hN, one_div, one_div, hpq.inv_add_inv_eq_one, Real.rpow_one]
  have hprod := mul_le_mul h1 h2 (Real.rpow_nonneg hA0 _)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKB _) (Real.rpow_nonneg hN.le _)) hAN)
  calc ∑ i ∈ S, b i * a i ≤ _ := h
    _ ≤ _ := hprod
    _ = KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) *
          (N ^ (1 / q) * N ^ (1 / Real.conjExponent q)) * (A / (F * N)) := by ring
    _ = KB ^ (1 / q) * KA ^ (1 / Real.conjExponent q) * (A / F) := by
        rw [hNN, mul_assoc _ N, show N * (A / (F * N)) = A / F * (N / N) by ring,
          div_self hN.ne', mul_one]

set_option maxHeartbeats 400000 in
/-- **The Caccioppoli step**: the energy of `u` on `□_{j+1}`, counted with the edges inside the
crossing cluster of `□_{j+2}`, is at most `8 d 3^{-2(j+1)} ∑_{C_*(□_{j+3})} (u - c)²`. -/
theorem energy_enl_le_caccioppoli_cube (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h2C : ∀ x ∈ crossingClusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hU3 : ∀ x ∈ triadicCubeFinset d (j + 2) 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0) (c : ℝ) :
    ∑ z ∈ enl 1 j (0 : Vertex d), clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u) z ≤
      8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - c) ^ 2 := by
  set f := Rigidity.Section3.extend C u with hfdef
  set S₂ := crossingClusterVertices ω ⟨j + 2, 0⟩ with hS₂
  set U := (triadicCubeFinset d (j + 2) 0).filter (· ∈ C.supp) with hUdef
  set V' := (triadicCubeFinset d (j + 1) 0).filter (· ∈ C.supp) with hV'def
  have hS₂U : S₂ ⊆ U := fun x hx => Finset.mem_filter.2
    ⟨mem_cubeFinset_of_mem_crossingClusterVertices hx, h2C x hx⟩
  have hV'U : V' ⊆ U := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨mem_cubeFinset_mono (by omega) hx1, hx2⟩
  -- the energy on `□_{j+1}` against the energy in `U`
  have hE : ∑ z ∈ enl 1 j (0 : Vertex d), clusterEnergy ω S₂ f z ≤
      ∑ z ∈ V', clusterGradSq ω U f z := by
    calc ∑ z ∈ enl 1 j (0 : Vertex d), clusterEnergy ω S₂ f z
        = ∑ z ∈ (enl 1 j (0 : Vertex d)).filter (· ∈ S₂), clusterGradSq ω S₂ f z := by
          rw [Finset.sum_filter]; rfl
      _ ≤ ∑ z ∈ (enl 1 j (0 : Vertex d)).filter (· ∈ S₂), clusterGradSq ω U f z :=
          Finset.sum_le_sum fun z _ => clusterGradSq_le_of_subset hS₂U f z
      _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
            fun _ _ _ => clusterGradSq_nonneg _ _ _ _
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          rw [enl_one_zero_eq_cube_succ] at hz1
          exact Finset.mem_filter.2 ⟨mem_cubeFinset_of_mem_cube_zero hz1, h2C z hz2⟩
  -- the Caccioppoli inequality on `U` from `V'`
  have hr : (0 : ℝ) < 3 ^ (j + 1) := by positivity
  have hdist : ∀ x ∈ V', ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) →
      (3 : ℝ) ^ (j + 1) ≤ (supDist x z : ℝ) := by
    rintro x hx z hz ⟨y, hzy, hyU⟩
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
    have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hz2 hzy
    have hy2 : y ∉ triadicCubeFinset d (j + 2) 0 := fun h => hyU (Finset.mem_filter.2 ⟨h, hyC⟩)
    rw [mem_cubeFinset_iff_int] at hy2
    push Not at hy2
    obtain ⟨k, hk⟩ := hy2
    have hzk := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hzy) k
    have hxk := (mem_cubeFinset_iff_int.1 hx1) k
    have hzk2 := (mem_cubeFinset_iff_int.1 hz1) k
    have hle : (x k - z k).natAbs ≤ supDist x z :=
      Finset.le_sup (f := fun i => (x i - z i).natAbs) (Finset.mem_univ k)
    have hcast : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ ((x k - z k).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      have h3 : (3 : ℤ) ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
      have hab := abs_sub_abs_le_abs_sub (z k) (x k)
      have hyz := abs_sub_abs_le_abs_sub (y k) (z k)
      rw [abs_sub_comm (z k) (x k)] at hab
      have hodd := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one (j + 2)
      generalize |x k| = a at hxk hab
      generalize |z k| = b at hzk2 hab hyz
      generalize |y k| = c at hk hyz
      generalize |x k - z k| = e at hab ⊢
      generalize |y k - z k| = g at hzk hyz
      generalize (3 : ℤ) ^ (j + 1) = t at h3 hxk ⊢
      generalize (3 : ℤ) ^ (j + 2) = t2 at h3 hk hzk2 hodd
      omega
    have : ((3 : ℤ) ^ (j + 1) : ℤ) ≤ (supDist x z : ℤ) := hcast.trans (by exact_mod_cast hle)
    exact_mod_cast this
  have hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) →
      openLaplacian ω (fun y => f y - c) x = 0 := by
    intro x hx _
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    rw [openLaplacian_sub_const, hfdef, openLaplacian_extend_eq_componentLaplacian C u hx2]
    exact hharm x hx2 (mem_cubeFinset_mono (by omega) hx1)
  have hcac := caccioppoli_cluster ω U V' hV'U hr hdist (fun y => f y - c) hu
  have e1 : ∑ x ∈ V', clusterGradSq ω U (fun y => f y - c) x =
      ∑ x ∈ V', clusterGradSq ω U f x :=
    Finset.sum_congr rfl fun x _ => clusterGradSq_sub_const_eq U f c x
  rw [e1] at hcac
  have hsumU : ∑ x ∈ U.filter (fun x => ¬ (x ∈ V' ∧
      ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V')), (f x - c) ^ 2 ≤
      ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, (f x - c) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun _ _ _ => sq_nonneg _
    obtain ⟨hxU, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hxU
    exact hU3 x hx1 hx2
  calc _ ≤ ∑ z ∈ V', clusterGradSq ω U f z := hE
    _ ≤ _ := hcac
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumU (by positivity)

set_option maxHeartbeats 400000 in
/-- **The comparison (7.8) in `L²` on one cube** (Armstrong–Dario, proof of Lemma 7.1, Step 3, in
dimension `d`): from Lemma 3.2 with the reach scales, the Hölder inequality with the moments of
the reach scales, the Meyers estimate `hM` on `□_j` for `u` on the crossing cluster of `□_{j+2}`,
and the Caccioppoli inequality on `𝒞 ∩ □_{j+2}`. -/
theorem coarseComparison_on_cube (hd : 0 < d) (hP : PartitionEvent ω) (C : OpenComponent ω)
    (u : C → ℝ) {j : ℕ} (hres0 : PartitionResolved ω ⟨j, 0⟩)
    (h02 : crossingClusterVertices ω ⟨j, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 2, 0⟩)
    (h2C : ∀ x ∈ crossingClusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hU3 : ∀ x ∈ triadicCubeFinset d (j + 2) 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    {q CM Kρ : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM) (hKρ : 0 ≤ Kρ)
    (hM : avg (cube j (0 : Vertex d)) (fun x => clusterEnergy ω
        (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) x ^ q) ≤
      CM * avg (enl 1 j (0 : Vertex d)) (clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u)) ^ q)
    (hmom : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        (((3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres0).reachScale z) ^ ((2 : ℝ) * d)) ^
          Real.conjExponent q ≤ Kρ * ((3 : ℝ) ^ j) ^ d) :
    clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - partitionCoarse C u x) ≤
      partitionCoarseConst d * Real.sqrt (8 * d * 9 ^ d) *
        Real.sqrt (CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q)) / 3 ^ j *
          clusterCubeOsc C u (j + 3) := by
  set f := Rigidity.Section3.extend C u with hfdef
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex d → ℝ,
      E = clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩) f := ⟨_, rfl⟩
  rw [← hEdef] at hM
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex d), E z := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  set N : ℝ := ((3 : ℝ) ^ j) ^ d with hNdef
  have hN : (0 : ℝ) < N := by positivity
  have hF : (0 : ℝ) < 3 ^ d := by positivity
  have hcube : ((cube j (0 : Vertex d)).card : ℝ) = N := card_cube j 0
  have henl : ((enl 1 j (0 : Vertex d)).card : ℝ) = 3 ^ d * N := by
    rw [card_enl, hNdef, ← mul_pow, pow_succ']
  set ρ := (partitionCoarseData hd hP ⟨j, 0⟩ hres0).reachScale with hρdef
  set Cc := partitionCoarseConst d with hCcdef
  -- Lemma 3.2
  have hL : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (f x - partitionCoarse C u x) ^ 2 ≤
      Cc ^ 2 * ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 := by
    have h := partition_sum_abs_sub_coarseAnchor_rpow_le hd hP hres0 f (s := 2) (by norm_num)
    have e1 : ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩,
        |f x - f (partitionAnchor ω x)| ^ (2 : ℝ) = (f x - partitionCoarse C u x) ^ 2 :=
      fun x _ => by rw [Real.rpow_two, sq_abs]; rfl
    have e2 : ∀ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ (2 : ℝ) =
        ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 :=
      fun z _ => by rw [Real.rpow_two]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Real.rpow_two] at h
    exact h
  -- the energy bound for the gradients on `C_*(□_j)`
  have hgE : ∀ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
      gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 ≤ E z := by
    intro z hz
    have hz2 := h02 hz
    rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
      split_ifs <;> positivity)), hEdef, clusterEnergy, if_pos hz2, clusterGradSq,
      ← Finset.sum_filter]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy2, h02 hy1⟩)
      fun _ _ _ => sq_nonneg _
  -- the Hölder step with the Meyers estimate
  have hbq : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
      (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2) ^ q ≤ CM * N * (A / (3 ^ d * N)) ^ q := by
    have hq0 : 0 ≤ q := by linarith
    calc ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
          (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2) ^ q
        ≤ ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, E z ^ q :=
          Finset.sum_le_sum fun z hz => Real.rpow_le_rpow (sq_nonneg _) (hgE z hz) hq0
      _ ≤ ∑ z ∈ cube j (0 : Vertex d), E z ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => mem_cube_zero_of_mem_cubeFinset
              (mem_cubeFinset_of_mem_crossingClusterVertices hz))
            fun z _ _ => Real.rpow_nonneg (hE0 z) _
      _ = N * avg (cube j (0 : Vertex d)) (fun x => E x ^ q) := by
          rw [avg, hcube]; field_simp
      _ ≤ N * (CM * avg (enl 1 j (0 : Vertex d)) E ^ q) :=
          mul_le_mul_of_nonneg_left hM hN.le
      _ = CM * N * (A / (3 ^ d * N)) ^ q := by
          rw [avg, henl, ← hAdef]; ring
  have hHold := holder_meyers_bound_of_factor (crossingClusterVertices ω ⟨j, 0⟩)
    (a := fun z => ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d))
    (b := fun z => gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2)
    (fun z _ => by positivity) (fun z _ => sq_nonneg _) hq hKρ hCM hN hA0 hF hbq hmom
  set P := CM ^ (1 / q) * Kρ ^ (1 / Real.conjExponent q) with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hsum : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (f x - partitionCoarse C u x) ^ 2 ≤
      Cc ^ 2 * P * (A / 3 ^ d) := by
    have e : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 =
        ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
          gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 *
            ((3 : ℝ) ^ ρ z) ^ ((2 : ℝ) * d) :=
      Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [e] at hL
    calc _ ≤ _ := hL
      _ ≤ Cc ^ 2 * (P * (A / 3 ^ d)) := mul_le_mul_of_nonneg_left hHold (sq_nonneg _)
      _ = Cc ^ 2 * P * (A / 3 ^ d) := by ring
  -- the bound for every constant
  have hCc0 : 0 ≤ Cc := partitionCoarseConst_nonneg d
  set K := Cc * Real.sqrt (8 * d * 9 ^ d) * Real.sqrt P with hKdef
  have hK0 : 0 ≤ K / 3 ^ j := by positivity
  rw [clusterCubeOsc, Real.mul_iInf_of_nonneg hK0]
  refine le_ciInf fun c => ?_
  have hcac := energy_enl_le_caccioppoli_cube C u h2C hU3 hharm c
  rw [← hfdef, ← hEdef, ← hAdef] at hcac
  set Ssum := ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, (f x - c) ^ 2 with hSsum
  have hSsum0 : 0 ≤ Ssum := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3j : (0 : ℝ) < 3 ^ j := by positivity
  have hfin : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (f x - partitionCoarse C u x) ^ 2 ≤
      Cc ^ 2 * P * (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum) / 3 ^ d := by
    have h1 := div_le_div_of_nonneg_right hcac hF.le
    calc _ ≤ Cc ^ 2 * P * (A / 3 ^ d) := hsum
      _ ≤ Cc ^ 2 * P * (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum / 3 ^ d) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hR : (K / 3 ^ j) ^ 2 * (Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) =
      Cc ^ 2 * P * (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum) / 3 ^ d / N * 9 := by
    have e27 : ((3 : ℝ) ^ (j + 3)) ^ d = 9 ^ d * 3 ^ d * N := by
      rw [hNdef, ← mul_pow, ← mul_pow, pow_add, mul_comm ((3 : ℝ) ^ j) (3 ^ 3)]; norm_num
    have hNne : N ≠ 0 := hN.ne'
    have e1 : ((3 : ℝ) ^ (j + 1)) ^ 2 = 9 * (3 ^ j) ^ 2 := by rw [pow_succ]; ring
    rw [hKdef, div_pow, mul_pow, mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt (by positivity), e27, e1]
    field_simp
  have key : (∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (f x - partitionCoarse C u x) ^ 2) / N ≤
      (K / 3 ^ j) ^ 2 * (Ssum / ((3 : ℝ) ^ (j + 3)) ^ d) := by
    rw [hR]
    have hX0 : 0 ≤ Cc ^ 2 * P * (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum) / 3 ^ d / N := by
      positivity
    calc _ ≤ Cc ^ 2 * P * (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum) / 3 ^ d / N :=
          div_le_div_of_nonneg_right hfin hN.le
      _ ≤ _ := le_mul_of_one_le_right hX0 (by norm_num)
  unfold clusterCubeL2
  rw [← Real.sqrt_sq hK0, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt key

/-- Harmonicity on `𝒞 ∩ □_{j+3}` from harmonicity on `𝒞 ∩ B_R`, `√d 3^{j+3} ≤ R`. -/
theorem harm_on_cube_of_isHarmonicInBall (hd : 0 < d) {C : OpenComponent ω} {R : ℝ} {u : C → ℝ}
    (hu : IsHarmonicInBall C R u) {j : ℕ} (hjR : Real.sqrt d * 3 ^ (j + 3) ≤ R) :
    ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0 := by
  intro x hx hxsq
  have hdx := dist_le_of_mem_cubeFinset hxsq
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h3 : (27 : ℝ) ≤ 3 ^ (j + 3) := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (j + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : Real.sqrt d * (3 ^ (j + 3) / 2) + Real.sqrt d * 1 < Real.sqrt d * 3 ^ (j + 3) := by
    have : (3 : ℝ) ^ (j + 3) / 2 + 1 < 3 ^ (j + 3) := by linarith
    nlinarith
  refine hu ⟨x, hx⟩ ?_ fun y hy => ?_
  · rw [mem_componentEuclideanBall]
    have : Real.sqrt d * (3 ^ (j + 3) / 2) < Real.sqrt d * 3 ^ (j + 3) := by linarith
    linarith
  · rw [mem_componentEuclideanBall]
    have hadj : (openGraph ω).Adj x y.val := hy
    have hy1 : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x) ≤
        Real.sqrt d * 1 := by
      apply dist_latticeEuclideanEmbedding_le zero_le_one
      intro i
      have := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hadj) i
      have e : (latticeEuclideanEmbedding x) i = (x i : ℝ) := rfl
      rw [e]
      exact_mod_cast this
    have := dist_triangle (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding (0 : Vertex d))
    linarith

/-- The reach scale moments on the crossing cluster of `□_j` from the moments of the reach on
the triadic cube of scale `j`. -/
theorem sum_reachScale_rpow_le_of_reach (hd : 0 < d) (hP : PartitionEvent ω) {j : ℕ}
    (hres : PartitionResolved ω ⟨j, 0⟩) {τ K : ℝ} (hτ : 0 < τ)
    (hfin : ∀ x ∈ cube j (0 : Vertex d), partitionReach ω x ≠ ⊤)
    (hsum : ∑ x ∈ cube j (0 : Vertex d), partitionReach ω x ^ ⌈τ⌉₊ ≤
      ENNReal.ofReal (K * (cube j (0 : Vertex d)).card)) (hK : 0 ≤ K) :
    ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤
      K * ((3 : ℝ) ^ j) ^ d := by
  have hsub : crossingClusterVertices ω ⟨j, 0⟩ ⊆ cube j (0 : Vertex d) := fun z hz =>
    mem_cube_zero_of_mem_cubeFinset (mem_cubeFinset_of_mem_crossingClusterVertices hz)
  have hpt : ∀ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z) ^ τ ≤
        (partitionReach ω z).toReal ^ ⌈τ⌉₊ := by
    intro z hz
    have hle := three_pow_reachScale_le_partitionReach hd hP hres hz
    have hle' : (3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z ≤
        (partitionReach ω z).toReal := by
      have := ENNReal.toReal_mono (hfin z (hsub hz)) hle
      simpa using this
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z :=
      one_le_pow₀ (by norm_num)
    calc ((3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z) ^ τ
        ≤ (partitionReach ω z).toReal ^ τ := Real.rpow_le_rpow (by positivity) hle' hτ.le
      _ ≤ (partitionReach ω z).toReal ^ (⌈τ⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (h1.trans hle') (Nat.le_ceil τ)
      _ = (partitionReach ω z).toReal ^ ⌈τ⌉₊ := Real.rpow_natCast _ _
  calc ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        ((3 : ℝ) ^ (partitionCoarseData hd hP ⟨j, 0⟩ hres).reachScale z) ^ τ
      ≤ ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, (partitionReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ z ∈ cube j (0 : Vertex d), (partitionReach ω z).toReal ^ ⌈τ⌉₊ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ z ∈ cube j (0 : Vertex d), partitionReach ω z ^ ⌈τ⌉₊).toReal := by
        rw [ENNReal.toReal_sum fun z hz => ENNReal.pow_ne_top (hfin z hz)]
        exact Finset.sum_congr rfl fun z _ => (ENNReal.toReal_pow _ _).symm
    _ ≤ (ENNReal.ofReal (K * (cube j (0 : Vertex d)).card)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = K * ((3 : ℝ) ^ j) ^ d := by
        rw [ENNReal.toReal_ofReal (by positivity), card_cube]

theorem two_mul_le_of_three_pow_le_rpow_half' {a m : ℕ}
    (h : (3 : ℝ) ^ a ≤ ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ)) : a * 2 ≤ m := by
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), ← pow_mul] at hsq
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hsq

set_option maxHeartbeats 400000 in
/-- **The scales of the partition cubes**: `CubePartitionSizeScale d p` from the second bound of
(2.13) of Proposition 2.4 with `t = d`. -/
theorem cubePartitionSizeScale_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : CubePartitionSizeScale d p := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨r, θ, hr, hθ, M, hMm, hM0, hMos, hae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc (d : ℝ) (by exact_mod_cast (show 1 ≤ d by omega))
  have hOs := IsOsBond.max hr hθ (by positivity) hMm measurable_const hMos
    (isOsBond_const (p := p) (d := d) (by norm_num : (0 : ℝ) < 81) hr)
  refine ⟨r, _, hr, by positivity, fun ω => max (M ω) 81, hMm.max measurable_const,
    fun ω => (hM0 ω).trans (le_max_left _ _), hOs, ?_⟩
  filter_upwards [hae, (partition_estimates hd hpc).1] with ω hω hP
  refine ⟨hP, fun m hm x hx => ?_⟩
  have hm1 : M ω ≤ 3 ^ m := (le_max_left _ _).trans hm
  have hm81 : (3 : ℝ) ^ 4 ≤ 3 ^ m := by
    have h81 : (81 : ℝ) ≤ 3 ^ m := (le_max_right _ _).trans hm
    calc (3 : ℝ) ^ 4 = 81 := by norm_num
      _ ≤ 3 ^ m := h81
  have hm4 : 4 ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hm81
  obtain ⟨-, hsize⟩ := hω m hm1
  have hb := hsize x (mem_cubeFinset_iff_vertices.1 hx)
  have e : (d : ℝ) * m / (d + d) = 1 / 2 * m := by field_simp; ring
  rw [e] at hb
  have hb' : (3 : ℝ) ^ (partitionCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), mul_comm]
    exact hb
  have h2 := two_mul_le_of_three_pow_le_rpow_half' hb'
  omega

end Rigidity.Proofs.Regularity
