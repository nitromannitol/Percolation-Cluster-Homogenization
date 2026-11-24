import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaCaccioppoli

/-!
# The pointwise chain of the proof of Lemma 5.9 of Armstrong and Dario, in every dimension

Let `V = □_n`, `U = □_{n+1}`, `n ≥ 1`, both resolved, on the partition event; let `u_V, u_U` be the
minimizers of `μ(·, q)` and `v_V, v_U` the maximizers of `ν(·, p)`. Following the proof of
Lemma 5.9 of Armstrong and Dario (displays (5.38)-(5.41)):

* quadratic response (5.38): `ν(V, p) - μ(V, q) - q · p ≤ B_V(v_V - u_V)/(2|V|) + |q · p|/L
  + |q|₁ E_p(v_V)/|V|` (`cubeNu_sub_cubeMu_sub_le_cubeForm`);
* `B_V(v_V - u_V) ≤ 3 (B_V(v_V - v_U) + B_V(v_U - u_U) + B_V(u_U - u_V))`, the outer terms being at
  most twice the energies of the differences of Lemma 5.4 (`cubeForm_add_add_le`);
* the Caccioppoli inequality for the harmonic function `w = v_U - u_U` (5.39);
* the coarsening `w - [w]_𝒫` (5.40), and `[w]_𝒫 - c = ([v_U]_𝒫 - ℓ_ξ - c_v) - ([u_U]_𝒫 - ℓ_ξ - c_u)`,
  whose mean squares are the flatness errors of Lemma 5.8 for any slope `ξ` (5.41).

Together (`cubeNu_sub_cubeMu_chain`):

`ν(V, p) - μ(V, q) - q · p ≤ |q · p| / L + |q|₁ E_p(v_V) / |V| + 3 (D^ν_n + D^μ_n) / |V|
  + 12 d ((3ⁿ - 1)² |V|)⁻¹ (2 ∑_{C_*(U)} |w - [w]_𝒫|² + 4 |U| (F_u + F_v))`.

The two-dimensional version is `Rigidity.Percolation.planarOmega_chain`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (finsetMean affineFun)

variable {d : ℕ} {ω : Configuration d}

/-- `B(a + b + c) ≤ 3 (B(a) + B(b) + B(c))` for the Dirichlet form of a cluster. -/
theorem cubeForm_add_add_le {U : TriadicCube d} (a b c : CubeFun ω U) :
    cubeForm ω U (a + b + c) (a + b + c) ≤
      3 * (cubeForm ω U a a + cubeForm ω U b b + cubeForm ω U c c) := by
  have h2 : ∀ x y : CubeFun ω U, 2 * cubeForm ω U x y ≤ cubeForm ω U x x + cubeForm ω U y y := by
    intro x y
    have h := cubeForm_self_nonneg (ω := ω) (x - y)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [cubeForm_symm y x] at h
    linarith
  have hab := h2 a b
  have hac := h2 a c
  have hbc := h2 b c
  have e : cubeForm ω U (a + b + c) (a + b + c) = cubeForm ω U a a + cubeForm ω U b b +
      cubeForm ω U c c + 2 * cubeForm ω U a b + 2 * cubeForm ω U a c + 2 * cubeForm ω U b c := by
    simp only [map_add, LinearMap.add_apply]
    rw [cubeForm_symm b a, cubeForm_symm c a, cubeForm_symm c b]
    ring
  rw [e]
  linarith

/-- **Quadratic response** (Armstrong and Dario, (5.38), pointwise) for the chosen minimizer of
`μ` and maximizer of `ν`. -/
theorem cubeNu_sub_cubeMu_sub_le_cubeForm (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (p q : Fin d → ℝ) :
    cubeNu ω U p - cubeMu ω U q - ∑ i, q i * p i ≤
      cubeForm ω U (cubeNuMaximizer ω U p - cubeMuMinimizer ω U q)
          (cubeNuMaximizer ω U p - cubeMuMinimizer ω U q) / 2 / U.latticeVolume +
        |∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
        (∑ i, |q i|) * cubeBoundaryError ω U p (cubeNuMaximizer ω U p) / U.latticeVolume := by
  set u := cubeMuMinimizer ω U q with hu
  set v := cubeNuMaximizer ω U p with hv
  obtain ⟨huA, hvar_u⟩ := cubeMuMinimizer_spec hd hP hU q
  obtain ⟨hvA, hvar_v⟩ := cubeNuMaximizer_spec (ω := ω) U p
  obtain ⟨c, hc⟩ := exists_affine_boundary_of_cubeNu_variation hd hP hU p hvar_v
  have hid := cubeNu_sub_cubeMu_eq hd hP hU p q huA hvar_u hvA hvar_v
  have hb := abs_cubeCoarsePairing_sub_le hd hP hU p q hc
  have hvol := U.latticeVolume_pos
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL0 : 0 < L := by
    rw [hL, U.cast_size_toIntegerCube]
    positivity
  have hLvol : L ^ (d - 1) * L = U.latticeVolume := by
    rw [U.latticeVolume_eq_size_pow, ← hL, ← pow_succ, Nat.sub_add_cancel hd]
  set s := ∑ i, q i * p i
  set E := (∑ i, |q i|) * cubeBoundaryError ω U p v
  set B := cubeForm ω U (v - u) (v - u)
  have key : cubeNu ω U p - cubeMu ω U q - s - B / 2 / U.latticeVolume =
      ((cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1))) - s * L ^ (d - 1)) /
        U.latticeVolume := by
    rw [eq_div_iff hvol.ne']
    rw [← hLvol] at hid ⊢
    have hB : B / 2 / (L ^ (d - 1) * L) * (L ^ (d - 1) * L) = B / 2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [hB]
  have hLd : 0 < L ^ (d - 1) := by positivity
  have h1 : (cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1))) - s * L ^ (d - 1) ≤
      E + |s| * L ^ (d - 1) := by
    have := le_abs_self (cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1)))
    have := neg_abs_le s
    nlinarith
  have h2 : cubeNu ω U p - cubeMu ω U q - s - B / 2 / U.latticeVolume ≤
      |s| / L + E / U.latticeVolume := by
    rw [key]
    have e : |s| / L + E / U.latticeVolume = (E + |s| * L ^ (d - 1)) / U.latticeVolume := by
      rw [← hLvol]
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right h1 hvol.le
  have e3 : E / U.latticeVolume =
      (∑ i, |q i|) * cubeBoundaryError ω U p v / U.latticeVolume := rfl
  linarith

/-- The restriction to a subcube is linear. -/
theorem cubeRestrictExt_sub (V : TriadicCube d) {U : TriadicCube d} (a b : CubeFun ω U) :
    cubeRestrictExt V (a - b) = cubeRestrictExt V a - cubeRestrictExt V b := by
  funext y
  simp only [cubeRestrictExt, Pi.sub_apply, map_sub]

/-- The energy on one resolved subcube of the difference of the minimizers is at most twice the
energy of the differences of Lemma 5.4. -/
theorem cubeForm_restrict_sub_le_cubeMuDefect (hP : PartitionEvent ω) {U V : TriadicCube d}
    {n : ℕ} (hU : PartitionResolved ω U) (hVm : V ∈ U.resolvedSubcubesAt ω n) (q : Fin d → ℝ) :
    cubeForm ω V (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
        (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) ≤
      2 * cubeMuDefect ω U n q := by
  rw [cubeMuDefect, if_pos ⟨hP, hU⟩]
  have h := Finset.single_le_sum (f := fun V' => cubeForm ω V'
      (cubeRestrictExt V' (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V' q)
      (cubeRestrictExt V' (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V' q) / 2)
    (fun V' _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num)) hVm
  linarith

/-- The same for the maximizers of `ν`. -/
theorem cubeForm_restrict_sub_le_cubeNuDefect {U V : TriadicCube d} {n : ℕ}
    (hVm : V ∈ U.resolvedSubcubesAt ω n) (p : Fin d → ℝ) :
    cubeForm ω V (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p)
        (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p) ≤
      2 * cubeNuDefect ω U n p := by
  rw [cubeNuDefect]
  have h := Finset.single_le_sum (f := fun V' => cubeForm ω V'
      (cubeRestrictExt V' (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V' p)
      (cubeRestrictExt V' (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V' p) / 2)
    (fun V' _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num)) hVm
  linarith

/-- The coarsening error `∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|²` of a function on the cluster. -/
noncomputable def cubeCoarseningError (ω : Configuration d) (U : TriadicCube d)
    (w : CubeFun ω U) : ℝ :=
  ∑ x ∈ crossingClusterVertices ω U,
    (cubeExtend ω U w x - cubeExtend ω U w (partitionAnchor ω x)) ^ 2

theorem cubeCoarseningError_nonneg (U : TriadicCube d) (w : CubeFun ω U) :
    0 ≤ cubeCoarseningError ω U w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The mean square deviation of the coarsening of a difference is controlled by the flatness errors
of the two coarsenings for the same slope. -/
theorem sum_sq_coarsen_sub_le_cubeFlatness (U : TriadicCube d) (a b : CubeFun ω U)
    (ξ : Fin d → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices, (cubeExtend ω U (a - b) (partitionAnchor ω x) -
        (finsetMean U.toIntegerCube.vertices (fun y =>
            cubeExtend ω U a (partitionAnchor ω y) - affineFun ξ y) -
          finsetMean U.toIntegerCube.vertices (fun y =>
            cubeExtend ω U b (partitionAnchor ω y) - affineFun ξ y))) ^ 2 ≤
      2 * U.latticeVolume *
        (cubeFlatnessError U (fun x => cubeExtend ω U a (partitionAnchor ω x)) ξ +
          cubeFlatnessError U (fun x => cubeExtend ω U b (partitionAnchor ω x)) ξ) := by
  set ca := finsetMean U.toIntegerCube.vertices (fun y =>
    cubeExtend ω U a (partitionAnchor ω y) - affineFun ξ y) with hca
  set cb := finsetMean U.toIntegerCube.vertices (fun y =>
    cubeExtend ω U b (partitionAnchor ω y) - affineFun ξ y) with hcb
  have hvol := U.latticeVolume_pos
  have hpt : ∀ x ∈ U.toIntegerCube.vertices,
      (cubeExtend ω U (a - b) (partitionAnchor ω x) - (ca - cb)) ^ 2 ≤
        2 * (cubeExtend ω U a (partitionAnchor ω x) - affineFun ξ x - ca) ^ 2 +
          2 * (cubeExtend ω U b (partitionAnchor ω x) - affineFun ξ x - cb) ^ 2 := by
    intro x _
    rw [map_sub, Pi.sub_apply]
    nlinarith [sq_nonneg ((cubeExtend ω U a (partitionAnchor ω x) - affineFun ξ x - ca) +
      (cubeExtend ω U b (partitionAnchor ω x) - affineFun ξ x - cb))]
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, cubeFlatnessError,
    cubeFlatnessError, ← hca, ← hcb]
  field_simp

/-- **The pointwise chain of the proof of Lemma 5.9** (Armstrong and Dario, (5.38)-(5.41), every
dimension `d ≥ 1`). -/
theorem cubeNu_sub_cubeMu_chain (hd : 0 < d) (hP : PartitionEvent ω) {n : ℕ} (hn : 1 ≤ n)
    (hU : PartitionResolved ω ⟨n + 1, 0⟩) (hV : PartitionResolved ω ⟨n, 0⟩)
    (p q ξ : Fin d → ℝ) :
    cubeNu ω ⟨n, 0⟩ p - cubeMu ω ⟨n, 0⟩ q - ∑ i, q i * p i ≤
      |∑ i, q i * p i| / ((⟨n, 0⟩ : TriadicCube d).toIntegerCube.size : ℝ) +
      (∑ i, |q i|) * cubeBoundaryError ω ⟨n, 0⟩ p (cubeNuMaximizer ω ⟨n, 0⟩ p) /
        (⟨n, 0⟩ : TriadicCube d).latticeVolume +
      3 * (cubeNuDefect ω ⟨n + 1, 0⟩ n p + cubeMuDefect ω ⟨n + 1, 0⟩ n q) /
        (⟨n, 0⟩ : TriadicCube d).latticeVolume +
      12 * d / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube d).latticeVolume) *
        (2 * cubeCoarseningError ω ⟨n + 1, 0⟩
            (cubeNuMaximizer ω ⟨n + 1, 0⟩ p - cubeMuMinimizer ω ⟨n + 1, 0⟩ q) +
          4 * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume *
            (cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
                (cubeNuMaximizer ω ⟨n + 1, 0⟩ p) (partitionAnchor ω x)) ξ +
              cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
                (cubeMuMinimizer ω ⟨n + 1, 0⟩ q) (partitionAnchor ω x)) ξ)) := by
  set V : TriadicCube d := ⟨n, 0⟩ with hVdef
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hUdef
  set uU := cubeMuMinimizer ω U q
  set uV := cubeMuMinimizer ω V q
  set vU := cubeNuMaximizer ω U p
  set vV := cubeNuMaximizer ω V p
  have hVm : V ∈ U.resolvedSubcubesAt ω n :=
    mem_resolvedSubcubesAt.2 ⟨originCube_mem_subcubesAt n, hV⟩
  have h1 := cubeNu_sub_cubeMu_sub_le_cubeForm hd hP hV p q
  -- the decomposition
  have hdec : vV - uV = (vV - cubeRestrictExt V vU) + cubeRestrictExt V (vU - uU) +
      (cubeRestrictExt V uU - uV) := by
    rw [cubeRestrictExt_sub]
    abel
  have hB3 := cubeForm_add_add_le (ω := ω) (U := V) (vV - cubeRestrictExt V vU)
    (cubeRestrictExt V (vU - uU)) (cubeRestrictExt V uU - uV)
  rw [← hdec] at hB3
  have hν : cubeForm ω V (vV - cubeRestrictExt V vU) (vV - cubeRestrictExt V vU) ≤
      2 * cubeNuDefect ω U n p := by
    have h := cubeForm_restrict_sub_le_cubeNuDefect (ω := ω) hVm p
    have e : vV - cubeRestrictExt V vU = -(cubeRestrictExt V vU - vV) := by abel
    have hneg : ∀ y : CubeFun ω V, cubeForm ω V (-y) (-y) = cubeForm ω V y y := fun y => by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rw [e, hneg]
    exact h
  have hμ := cubeForm_restrict_sub_le_cubeMuDefect hP hU hVm q
  -- the Caccioppoli inequality
  set w := vU - uU with hw
  have hwA : w ∈ cubeHarmonic ω U :=
    sub_mem (cubeNuMaximizer_spec (ω := ω) U p).1 (cubeMuMinimizer_spec hd hP hU q).1
  set cv := finsetMean U.toIntegerCube.vertices (fun y =>
    cubeExtend ω U vU (partitionAnchor ω y) - affineFun ξ y) with hcv
  set cu := finsetMean U.toIntegerCube.vertices (fun y =>
    cubeExtend ω U uU (partitionAnchor ω y) - affineFun ξ y) with hcu
  have hcac := cubeForm_restrict_le_caccioppoli hd hP hn hV hwA (cv - cu)
  -- the coarsening and the flatness
  have hsplit : ∑ x ∈ crossingClusterVertices ω U, (cubeExtend ω U w x - (cv - cu)) ^ 2 ≤
      2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
        (cubeFlatnessError U (fun x => cubeExtend ω U vU (partitionAnchor ω x)) ξ +
          cubeFlatnessError U (fun x => cubeExtend ω U uU (partitionAnchor ω x)) ξ) := by
    have hpt : ∀ x ∈ crossingClusterVertices ω U, (cubeExtend ω U w x - (cv - cu)) ^ 2 ≤
        2 * (cubeExtend ω U w x - cubeExtend ω U w (partitionAnchor ω x)) ^ 2 +
          2 * (cubeExtend ω U w (partitionAnchor ω x) - (cv - cu)) ^ 2 := fun x _ => by
      nlinarith [sq_nonneg ((cubeExtend ω U w x - cubeExtend ω U w (partitionAnchor ω x)) -
        (cubeExtend ω U w (partitionAnchor ω x) - (cv - cu)))]
    have hsub : crossingClusterVertices ω U ⊆ U.toIntegerCube.vertices := Finset.filter_subset _ _
    have h2 : ∑ x ∈ crossingClusterVertices ω U,
        (cubeExtend ω U w (partitionAnchor ω x) - (cv - cu)) ^ 2 ≤
        ∑ x ∈ U.toIntegerCube.vertices, (cubeExtend ω U w (partitionAnchor ω x) - (cv - cu)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have h3 := sum_sq_coarsen_sub_le_cubeFlatness (ω := ω) U vU uU ξ
    rw [← hcv, ← hcu] at h3
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold cubeCoarseningError
    nlinarith
  have hvol := V.latticeVolume_pos
  have h3n : (1 : ℝ) < 3 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (0 : ℝ) < ((3 : ℝ) ^ n - 1) ^ 2 := by
    have : (0 : ℝ) < 3 ^ n - 1 := by linarith
    positivity
  have hK0 : 0 ≤ 8 * (d : ℝ) / ((3 : ℝ) ^ n - 1) ^ 2 := by positivity
  have hcac' := hcac.trans (mul_le_mul_of_nonneg_left hsplit hK0)
  have hBV : cubeForm ω V (vV - uV) (vV - uV) ≤
      3 * (2 * cubeNuDefect ω U n p + 8 * d / ((3 : ℝ) ^ n - 1) ^ 2 *
        (2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
          (cubeFlatnessError U (fun x => cubeExtend ω U vU (partitionAnchor ω x)) ξ +
            cubeFlatnessError U (fun x => cubeExtend ω U uU (partitionAnchor ω x)) ξ)) +
        2 * cubeMuDefect ω U n q) := by
    refine hB3.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    linarith
  have e : cubeForm ω V (vV - uV) (vV - uV) / 2 / V.latticeVolume ≤
      3 * (cubeNuDefect ω U n p + cubeMuDefect ω U n q) / V.latticeVolume +
      12 * d / (((3 : ℝ) ^ n - 1) ^ 2 * V.latticeVolume) *
        (2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
          (cubeFlatnessError U (fun x => cubeExtend ω U vU (partitionAnchor ω x)) ξ +
            cubeFlatnessError U (fun x => cubeExtend ω U uU (partitionAnchor ω x)) ξ)) := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have e2 : (3 * (cubeNuDefect ω U n p + cubeMuDefect ω U n q) / V.latticeVolume +
        12 * d / (((3 : ℝ) ^ n - 1) ^ 2 * V.latticeVolume) *
          (2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
            (cubeFlatnessError U (fun x => cubeExtend ω U vU (partitionAnchor ω x)) ξ +
              cubeFlatnessError U (fun x => cubeExtend ω U uU (partitionAnchor ω x)) ξ))) *
        (2 * V.latticeVolume) =
        3 * (2 * cubeNuDefect ω U n p + 8 * d / ((3 : ℝ) ^ n - 1) ^ 2 *
          (2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
            (cubeFlatnessError U (fun x => cubeExtend ω U vU (partitionAnchor ω x)) ξ +
              cubeFlatnessError U (fun x => cubeExtend ω U uU (partitionAnchor ω x)) ξ)) +
          2 * cubeMuDefect ω U n q) := by
      field_simp
      ring
    rw [e2]
    exact hBV
  linarith

end Rigidity.Percolation
