import PercolationClusterHomogenization.Proofs.Cluster.GeneralWeakConvHolds
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessNuExpect

/-!
# Lemma 5.8 of Armstrong and Dario for `μ`, in every dimension

Let `u = u(·, □_{n+1}, q)` be the minimizer of `μ(□_{n+1}, q)` (zero off the resolution of
`□_{n+1}`) and `[u]_𝒫` its coarsening. The multiscale Poincaré inequality, with the block averages
of `∇[u]_𝒫` on the subcubes `V` of scale `k` split as in display (5.36) of Armstrong and Dario,

`|V|⁻¹ ⟨∇[u]_𝒫⟩_V - ξ = |V|⁻¹ (⟨∇[u]_𝒫⟩_V - ⟨∇[u(·, V, q)]_𝒫⟩_V) + (|V|⁻¹ ⟨∇[u(·, V, q)]_𝒫⟩_V - ξ)`,

`ξ = ā_{□_n}⁻¹ q` (`exists_cubeMuFlatness_le_pointwise`), together with the energy bound (4.24)
(`exists_lintegral_coarse_cubeMuMinimizer_le`), Lemma 5.5 (`exists_lintegral_cubeMuRestrictError_le`),
Lemma 5.7 (`exists_lintegral_cubeMuGradAvg_sub_le`, around `ā_{□_k}⁻¹ q`) and the rate of
`ā_{□_k}⁻¹ - ā_{□_n}⁻¹` (`exists_sum_sq_cubeAhomInvFinite_mulVec_sub_le`) gives

`E[|□_{n+1}|⁻¹ ∑_{x ∈ □_{n+1}} |[u]_𝒫(x) - x · ā_{□_n}⁻¹ q - c|²]
  ≤ C |q|² 9ⁿ (3^{-n/4} + 3^{-n} ∑_{k ≤ n} 3^k τ_k)`

(`exists_lintegral_cubeMuFlatness_le`), `c` the mean of `[u]_𝒫 - ℓ_ξ` over `□_{n+1}`: display (5.32)
of Lemma 5.8 of Armstrong and Dario, in every dimension `d ≥ 2`. The differences of the coarsened
minimizers across the edges being measurable (`measurable_cubeMuMinimizer_edge`), so are the energy
and the quantity of Lemma 5.5. The two-dimensional version is
`Rigidity.Percolation.exists_lintegral_planarMuFlatness_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **The subcube averages of the coarsened gradient of a minimizer of `μ`**, split as in the
proof of (5.36) of Armstrong and Dario. -/
theorem sum_centers_coarsen_mu_le_general {m k : ℕ} (hk : k ≤ m) (z : Vertex d)
    (q ξ c : Fin d → ℝ) :
    ((Rigidity.Proofs.Multiscale.centers m z k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m z k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y)
            (fun x => cubeExtend ω ⟨m, z⟩ (cubeMuMinimizer ω ⟨m, z⟩ q) (partitionAnchor ω x)) j -
              ξ j) ^ 2 ≤
      3 * cubeMuRestrictError ω ⟨m, z⟩ k q +
      3 * ((((⟨m, z⟩ : TriadicCube d).subcubesAt k).card : ℝ)⁻¹ *
        ∑ V ∈ (⟨m, z⟩ : TriadicCube d).subcubesAt k, ∑ j : Fin d,
          (cubeMuGradAvg ω V q j - c j) ^ 2) +
      3 * ∑ j : Fin d, (c j - ξ j) ^ 2 := by
  set U : TriadicCube d := ⟨m, z⟩ with hU
  set w : Vertex d → ℝ := fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)
    with hw
  have hcard := card_subcubesAt_eq_general (d := d) hk z
  rw [← hU] at hcard
  have hc : (0 : ℝ) < (Rigidity.Proofs.Multiscale.centers m z k).card := by
    rw [Rigidity.Proofs.Multiscale.card_centers hk]
    positivity
  rw [Rigidity.Proofs.Multiscale.sum_centers hk z (fun B => ∑ j : Fin d,
    ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum B w j - ξ j) ^ 2)]
  rw [cubeMuRestrictError, cubeRestrictError, hcard]
  rw [sum_subcubesAt_eq_general hk z, sum_subcubesAt_eq_general hk z]
  set N : ℝ := ((Rigidity.Proofs.Multiscale.centers m z k).card : ℝ) with hN
  have hterm : ∀ j ∈ Rigidity.Proofs.Multiscale.cube (m - k) z,
      ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
        Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i - ξ i) ^ 2 ≤
        3 * ∑ i : Fin d, ((latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
            (fun _ => Pi.single i 1) (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
              (partitionAnchor ω x)) -
          cubeCoarsePairing ω ⟨k, j⟩ (Pi.single i 1) (cubeMuMinimizer ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube d).latticeVolume) ^ 2 +
        3 * ∑ i : Fin d, (cubeMuGradAvg ω ⟨k, j⟩ q i - c i) ^ 2 +
        3 * ∑ i : Fin d, (c i - ξ i) ^ 2 := by
    intro j _
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hvol : (⟨k, j⟩ : TriadicCube d).latticeVolume = ((3 : ℝ) ^ k) ^ d := rfl
    have hG : Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i =
        latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
          (fun _ => Pi.single i 1) w := gradSum_eq_latticeEdgePairing _ w i
    have e : (((3 : ℝ) ^ k) ^ d)⁻¹ *
        Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i - ξ i =
        (latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
            (fun _ => Pi.single i 1) w -
          cubeCoarsePairing ω ⟨k, j⟩ (Pi.single i 1) (cubeMuMinimizer ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube d).latticeVolume +
        (cubeMuGradAvg ω ⟨k, j⟩ q i - c i) + (c i - ξ i) := by
      rw [cubeMuGradAvg, hvol, hG]
      have : (0 : ℝ) < ((3 : ℝ) ^ k) ^ d := by positivity
      field_simp
      ring
    rw [e]
    exact add_add_sq_le_three_mul _ _ _
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const] at hsum
  have hcube : ((Rigidity.Proofs.Multiscale.cube (m - k) z).card : ℝ) = N := by
    rw [hN, Rigidity.Proofs.Multiscale.card_centers hk, Rigidity.Proofs.Multiscale.card_cube]
  rw [nsmul_eq_mul, hcube] at hsum
  exact inv_mul_le_of_le_three_mul hc hsum

/-- **The pointwise bound of the proof of Lemma 5.8 for `μ`**: the multiscale Poincaré inequality
for the coarsened minimizer of `μ(□_m, q)`, with the subcube averages split as in (5.36) of
Armstrong and Dario around arbitrary vectors `c_k`. -/
theorem exists_cubeMuFlatness_le_pointwise :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (m n₀ : ℕ), (m : ℝ) / 2 ≤ n₀ → n₀ ≤ m →
      ∀ (ω : Configuration d) (q ξ : Fin d → ℝ) (c : ℕ → Fin d → ℝ),
      cubeFlatnessError ⟨m, 0⟩ (fun x => cubeExtend ω ⟨m, 0⟩ (cubeMuMinimizer ω ⟨m, 0⟩ q)
          (partitionAnchor ω x)) ξ ≤
        (CM * (3 : ℝ) ^ (2 * n₀)) * cubeCoarseEnergy ω ⟨m, 0⟩ (cubeMuMinimizer ω ⟨m, 0⟩ q) +
        ∑ k ∈ Finset.Ico n₀ m, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
          (cubeMuRestrictError ω ⟨m, 0⟩ k q +
            (((⟨m, 0⟩ : TriadicCube d).subcubesAt k).card : ℝ)⁻¹ *
              ∑ V ∈ (⟨m, 0⟩ : TriadicCube d).subcubesAt k, ∑ j : Fin d,
                (cubeMuGradAvg ω V q j - c k j) ^ 2) +
        (CM * (3 : ℝ) ^ (2 * n₀) * ∑ i, ξ i ^ 2 +
          ∑ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (3 * ∑ j : Fin d, (c k j - ξ j) ^ 2 + (((3 : ℝ) ^ k) ^ 2)⁻¹ * ∑ i, ξ i ^ 2)) := by
  obtain ⟨CM, hCM, hM⟩ := exists_cubeFlatness_le_multiscale (d := d)
  refine ⟨CM, hCM, fun m n₀ hn₀2 hn₀m ω q ξ c => ?_⟩
  set U : TriadicCube d := ⟨m, 0⟩ with hU
  set s := Finset.Ico n₀ m with hs
  set Ξ := ∑ i, ξ i ^ 2 with hΞ
  set E : ℝ := cubeCoarseEnergy ω U (cubeMuMinimizer ω U q) with hE
  set A : ℕ → ℝ := fun k => cubeMuRestrictError ω U k q with hAdef
  set B : ℕ → ℝ := fun k =>
    (((U.subcubesAt k).card : ℝ))⁻¹ * ∑ V ∈ U.subcubesAt k, ∑ j : Fin d,
      (cubeMuGradAvg ω V q j - c k j) ^ 2 with hBdef
  set Cc : ℕ → ℝ := fun k => ∑ j : Fin d, (c k j - ξ j) ^ 2 with hCc
  change cubeFlatnessError U (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
        (partitionAnchor ω x)) ξ ≤
      (CM * (3 : ℝ) ^ (2 * n₀)) * E + ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
        (A k + B k) +
      (CM * (3 : ℝ) ^ (2 * n₀) * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ))
  have hvol : U.latticeVolume =
      ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ) := by
    rw [show Rigidity.Proofs.Multiscale.cube m (0 : Vertex d) = U.toIntegerCube.vertices from rfl,
      U.card_toIntegerCube_vertices]
  set w : Vertex d → ℝ := fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)
    with hw
  have h1 := hM m n₀ hn₀2 hn₀m 0 w ξ
  have hflat : cubeFlatnessError U w ξ =
      ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ)⁻¹ *
        ∑ x ∈ Rigidity.Proofs.Multiscale.cube m (0 : Vertex d),
        (w x - Rigidity.Proofs.Multiscale.affineFun ξ x -
          Rigidity.Proofs.Multiscale.finsetMean (Rigidity.Proofs.Multiscale.cube m (0 : Vertex d))
            (fun y => w y - Rigidity.Proofs.Multiscale.affineFun ξ y)) ^ 2 := by
    rw [cubeFlatnessError, hvol]
    rfl
  have hEω : ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ)⁻¹ *
      ∑ x ∈ Rigidity.Proofs.Multiscale.cube m (0 : Vertex d),
        Rigidity.Proofs.Multiscale.gradNormSq (Rigidity.Proofs.Multiscale.cube m (0 : Vertex d))
          w x = E := by
    simp only [hE, cubeCoarseEnergy, hvol]
    rfl
  rw [hflat]
  rw [hEω, ← hΞ] at h1
  refine h1.trans ?_
  have hk : ∀ k ∈ s, (3 : ℝ) ^ k *
      (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y) w j - ξ j) ^ 2 +
        (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) ≤
      3 * (3 : ℝ) ^ k * (A k + B k) + (3 : ℝ) ^ k * (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) := by
    intro k hks
    have hkm : k ≤ m := (Finset.mem_Ico.1 hks).2.le
    have h2 := sum_centers_coarsen_mu_le_general (ω := ω) hkm 0 q ξ (c k)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 3 ^ k by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum hk
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ CM * (3 : ℝ) ^ m by positivity)
  rw [Finset.mul_sum, Finset.mul_sum] at hsum'
  have e1 : ∑ i ∈ s, CM * (3 : ℝ) ^ m * (3 * (3 : ℝ) ^ i * (A i + B i) +
      (3 : ℝ) ^ i * (3 * Cc i + (((3 : ℝ) ^ i) ^ 2)⁻¹ * Ξ)) =
      ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) * (A k + B k) +
      ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1] at hsum'
  have hE0 : 0 ≤ E := cubeCoarseEnergy_nonneg U (cubeMuMinimizer ω U q)
  have e3 : CM * (3 : ℝ) ^ (2 * n₀) * (E + Ξ) =
      CM * (3 : ℝ) ^ (2 * n₀) * E + CM * (3 : ℝ) ^ (2 * n₀) * Ξ := by ring
  have e2 : CM * (3 : ℝ) ^ m * ∑ k ∈ s, (3 : ℝ) ^ k *
      (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y) w j - ξ j) ^ 2 +
        (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) =
      ∑ i ∈ s, CM * (3 : ℝ) ^ m * ((3 : ℝ) ^ i *
        (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) i).card : ℝ)⁻¹ *
          ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) i, ∑ j : Fin d,
            ((((3 : ℝ) ^ i) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
              (Rigidity.Proofs.Multiscale.subcube i y) w j - ξ j) ^ 2 +
          (((3 : ℝ) ^ i) ^ 2)⁻¹ * Ξ)) := by
    rw [Finset.mul_sum]
  linarith


section Expectation

variable {p : unitInterval}

theorem aemeasurable_cubeCoarseEnergy_cubeMuMinimizer (hd : 0 < d) (V : TriadicCube d)
    (q : Fin d → ℝ) :
    AEMeasurable (fun ω => cubeCoarseEnergy ω V (cubeMuMinimizer ω V q)) (latticeBondLaw d p) := by
  unfold cubeCoarseEnergy
  exact (aemeasurable_sum_gradNormSq_of_edge
    (F := fun ω x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) _
    fun x hx i hxi => (measurable_cubeMuMinimizer_edge hd V q hx hxi).aemeasurable).const_mul _

theorem aemeasurable_cubeMuRestrictError (hd : 0 < d) {U : TriadicCube d} {k : ℕ}
    (hk : k ≤ U.scale) (q : Fin d → ℝ) :
    AEMeasurable (fun ω => cubeMuRestrictError ω U k q) (latticeBondLaw d p) := by
  unfold cubeMuRestrictError cubeRestrictError
  refine (Finset.aemeasurable_fun_sum _ fun V hV =>
    Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
  have hVU := TriadicCube.subset_of_mem_subcubesAt hk hV
  have hsub : V.toIntegerCube.vertices ⊆ U.toIntegerCube.vertices := fun x hx =>
    (TriadicCube.mem_toIntegerCube_vertices U x).2
      (hVU ((TriadicCube.mem_toIntegerCube_vertices V x).1 hx))
  simp only [cubeCoarsePairing_eq_latticeEdgePairing]
  exact ((((measurable_latticeEdgePairing_cubeMuMinimizer hd hsub _ q).sub
    (measurable_latticeEdgePairing_cubeMuMinimizer hd subset_rfl _ q)).div_const _).pow_const
      2).aemeasurable

/-- **The matrices `ā_{□_n}⁻¹` are uniformly bounded.** -/
theorem exists_abs_cubeAhomInvFinite_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ (m : ℕ) (i j : Fin d), |cubeAhomInvFinite p m i j| ≤ KA := by
  obtain ⟨C, hC, h⟩ := exists_abs_cubeAhomInvFinite_sub_le hd hpc
  have hs := summable_cubeTau hd hpc
  set T := ∑' k, cubeTau (d := d) p k with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun k => cubeTau_nonneg p k
  set A0 := ∑ i : Fin d, ∑ j : Fin d, |cubeAhomInvFinite (d := d) p 0 i j| with hA0
  refine ⟨A0 + C * (T + 1), by positivity, fun m i j => ?_⟩
  have h1 := h 0 m (Nat.zero_le m) i j
  have hsum : ∑ k ∈ Finset.Ico 0 m, cubeTau (d := d) p k ≤ T :=
    hs.sum_le_tsum _ fun k _ => cubeTau_nonneg p k
  have h3 : 1 / √(√((3 : ℝ) ^ 0)) = 1 := by simp
  rw [h3] at h1
  have hij : |cubeAhomInvFinite (d := d) p 0 i j| ≤ A0 := by
    rw [hA0]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin d,
      |cubeAhomInvFinite (d := d) p 0 i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |cubeAhomInvFinite (d := d) p 0 i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  calc |cubeAhomInvFinite p m i j|
      ≤ |cubeAhomInvFinite p m i j - cubeAhomInvFinite p 0 i j| + |cubeAhomInvFinite (d := d) p 0 i j| := by
        have := abs_sub_abs_le_abs_sub (cubeAhomInvFinite (d := d) p m i j)
          (cubeAhomInvFinite p 0 i j)
        linarith
    _ ≤ C * (T + 1) + A0 := add_le_add (h1.trans (mul_le_mul_of_nonneg_left (by linarith) hC)) hij
    _ = A0 + C * (T + 1) := by ring

/-- **The rate of `ā_{□_k}⁻¹ q - ā_{□_n}⁻¹ q`**: for `k ≤ n`,
`|ā_{□_k}⁻¹ q - ā_{□_n}⁻¹ q|² ≤ C |q|² (∑_{l=k}^{n} τ_l + 3^{-k/4})`. -/
theorem exists_sum_sq_cubeAhomInvFinite_mulVec_sub_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ), k ≤ n → ∀ q : Fin d → ℝ,
      ∑ i, ((cubeAhomInvFinite p k *ᵥ q) i - (cubeAhomInvFinite p n *ᵥ q) i) ^ 2 ≤
        C * (∑ i, q i ^ 2) * (∑ l ∈ Finset.Ico k (n + 1), cubeTau (d := d) p l +
          (3 : ℝ) ^ (-(k : ℝ) / 4)) := by
  obtain ⟨CA, hCA, h⟩ := exists_abs_cubeAhomInvFinite_sub_le hd hpc
  have hs := summable_cubeTau hd hpc
  set T := ∑' k, cubeTau (d := d) p k with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun k => cubeTau_nonneg p k
  refine ⟨d ^ 2 * CA ^ 2 * (T + 1), by positivity, fun k n hkn q => ?_⟩
  set R := ∑ l ∈ Finset.Ico k n, cubeTau (d := d) p l + 1 / √(√((3 : ℝ) ^ k)) with hR
  set T' := ∑ l ∈ Finset.Ico k (n + 1), cubeTau (d := d) p l + (3 : ℝ) ^ (-(k : ℝ) / 4) with hT'
  have hR0 : 0 ≤ R := add_nonneg (Finset.sum_nonneg fun l _ => cubeTau_nonneg p l) (by positivity)
  have hRT' : R ≤ T' := by
    rw [hR, hT', ← three_rpow_neg_div_four_eq]
    exact add_le_add (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_right (Nat.le_succ n)) fun l _ _ => cubeTau_nonneg p l) le_rfl
  have hRT : R ≤ T + 1 := by
    have h1 : ∑ l ∈ Finset.Ico k n, cubeTau (d := d) p l ≤ T :=
      hs.sum_le_tsum _ fun l _ => cubeTau_nonneg p l
    have h2 : 1 / √(√((3 : ℝ) ^ k)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ √((3 : ℝ) ^ k) := Real.one_le_sqrt.2 (one_le_pow₀ (by norm_num))
      exact Real.one_le_sqrt.2 this
    linarith
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hentry : ∀ i, |(cubeAhomInvFinite p k *ᵥ q) i - (cubeAhomInvFinite p n *ᵥ q) i| ≤
      CA * R * Q := by
    intro i
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← sub_mul, abs_mul]
    have := h k n hkn i j
    rw [abs_sub_comm] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hsq : ∑ i, ((cubeAhomInvFinite p k *ᵥ q) i - (cubeAhomInvFinite p n *ᵥ q) i) ^ 2 ≤
      d * (CA * R * Q) ^ 2 := by
    calc _ ≤ ∑ _i : Fin d, (CA * R * Q) ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hentry i) 2
      _ = d * (CA * R * Q) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQ2 : Q ^ 2 ≤ d * ∑ i, q i ^ 2 := sq_sum_abs_le_card_mul q
  refine hsq.trans ?_
  have hR2 : R ^ 2 ≤ (T + 1) * T' := by
    calc R ^ 2 = R * R := sq R
      _ ≤ (T + 1) * T' := mul_le_mul hRT hRT' hR0 (by positivity)
  calc (d : ℝ) * (CA * R * Q) ^ 2 = d * CA ^ 2 * R ^ 2 * Q ^ 2 := by ring
    _ ≤ d * CA ^ 2 * ((T + 1) * T') * (d * ∑ i, q i ^ 2) := by
        have hT'0 : 0 ≤ T' := le_trans hR0 hRT'
        exact mul_le_mul (mul_le_mul_of_nonneg_left hR2 (by positivity)) hQ2 (sq_nonneg _)
          (by positivity)
    _ = d ^ 2 * CA ^ 2 * (T + 1) * (∑ i, q i ^ 2) * T' := by ring

/-- **Display (5.32) of Armstrong and Dario** (Lemma 5.8 for `μ`), in every dimension `d ≥ 2`: the
expected mean square deviation of `[u(·, □_{n+1}, q)]_𝒫` from the affine function of slope
`ā_{□_n}⁻¹ q` is at most `C |q|² 9^n (3^{-n/4} + 3^{-n} ∑_{k ≤ n} 3^k τ_k)`. -/
theorem exists_lintegral_cubeMuFlatness_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (cubeFlatnessError ⟨n + 1, 0⟩
          (fun x => cubeExtend ω ⟨n + 1, 0⟩ (cubeMuMinimizer ω ⟨n + 1, 0⟩ q) (partitionAnchor ω x))
          (cubeAhomInvFinite p n *ᵥ q)) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * (9 : ℝ) ^ n *
          ((3 : ℝ) ^ (-(n : ℝ) / 4) +
            ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨CE, hCE, hEn⟩ := exists_lintegral_coarse_cubeMuMinimizer_le hd hpc (a := 2 * d)
    (by omega)
  obtain ⟨C55, hC55, h55⟩ := exists_lintegral_cubeMuRestrictError_le hd hpc
  obtain ⟨C57, hC57, h57⟩ := exists_lintegral_cubeMuGradAvg_sub_le hd hpc
  obtain ⟨CS, hCS, hrate⟩ := exists_sum_sq_cubeAhomInvFinite_mulVec_sub_le hd hpc
  obtain ⟨KA, hKA, hKAb⟩ := exists_abs_cubeAhomInvFinite_le hd hpc
  obtain ⟨CM, hCM, hpw⟩ := exists_cubeMuFlatness_le_pointwise (d := d)
  set K : ℝ := d ^ 5 * KA ^ 2 + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : 1 ≤ K := by
    have : 0 ≤ (d : ℝ) ^ 5 * KA ^ 2 := by positivity
    rw [hK]
    linarith
  set L : ℝ := 27 * 3 ^ (3 * d) with hL
  have hL0 : 0 ≤ L := by positivity
  set Cf : ℝ := C55 + 2 * C57 + 2 * CS with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨CM * (CE + 1) * K * L + 9 * (3 * CM * (Cf + 0 * K) + CM * K), by positivity,
    fun n q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  set ξ := cubeAhomInvFinite p n *ᵥ q with hξ
  set Q := ∑ i, q i ^ 2 with hQdef
  set Ξ₂ := ∑ i, ξ i ^ 2 with hΞ₂def
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hΞ₂0 : 0 ≤ Ξ₂ := Finset.sum_nonneg fun i _ => sq_nonneg (ξ i)
  have hΞ₂K : Ξ₂ ≤ K * Q := by
    have h1 := sum_abs_mulVec_le (cubeAhomInvFinite (d := d) p n) q
    have hsumA : ∑ i, ∑ j, |cubeAhomInvFinite (d := d) p n i j| ≤ d ^ 2 * KA := by
      calc _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, KA :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hKAb n i j
        _ = d ^ 2 * KA := by simp [Finset.sum_const, Finset.card_univ]; ring
    have h2 := sq_sum_abs_le_card_mul q
    have h3 : (0 : ℝ) ≤ ∑ i, |ξ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hq1 : (0 : ℝ) ≤ ∑ i, |q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    calc Ξ₂ ≤ (∑ i, |ξ i|) ^ 2 := sum_sq_le_sq_sum_abs_vec ξ
      _ ≤ (d ^ 2 * KA * ∑ i, |q i|) ^ 2 := by
          refine pow_le_pow_left₀ h3 (h1.trans ?_) 2
          exact mul_le_mul_of_nonneg_right hsumA hq1
      _ = d ^ 4 * KA ^ 2 * (∑ i, |q i|) ^ 2 := by ring
      _ ≤ d ^ 4 * KA ^ 2 * (d * Q) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = d ^ 5 * KA ^ 2 * Q := by ring
      _ ≤ K * Q := by rw [hK]; nlinarith
  obtain ⟨n₀, hn₀a, hn₀m, hks, hn₀E⟩ : ∃ n₀ : ℕ, n + 1 ≤ 2 * n₀ ∧ n₀ ≤ n + 1 ∧
      (∀ k, n₀ ≤ k → k < n + 1 → 2 * d ≤ k ∧ n + 1 ≤ 2 * k) ∧
      4 * (2 * n₀) + 2 * (n + 1) ≤ 12 + 12 * d + 7 * n := by
    by_cases h : n + 1 < 4 * d
    · exact ⟨n + 1, by omega, le_rfl, fun k h1 h2 => by omega, by omega⟩
    · exact ⟨(n + 2) / 2, by omega, by omega, fun k h1 h2 => by omega, by omega⟩
  have hn₀2 : ((n + 1 : ℕ) : ℝ) / 2 ≤ n₀ := by
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n₀ : ℕ) : ℝ) := by exact_mod_cast hn₀a
    push_cast at this ⊢
    linarith
  set s := Finset.Ico n₀ (n + 1) with hs
  have hvol : U.latticeVolume = ((3 : ℝ) ^ (n + 1)) ^ d := rfl
  have hvol0 := U.latticeVolume_pos
  have hvne : U.latticeVolume ≠ 0 := hvol0.ne'
  have I₀ : ∫⁻ ω, ENNReal.ofReal (cubeCoarseEnergy ω U (cubeMuMinimizer ω U q)) ∂μ ≤
      ENNReal.ofReal (CE * (K * Q) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
    have hpt : ∀ ω, ENNReal.ofReal (cubeCoarseEnergy ω U (cubeMuMinimizer ω U q)) =
        ENNReal.ofReal U.latticeVolume⁻¹ * ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2) := by
      intro ω
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hvol0.le), cubeCoarseEnergy]
      congr 2
      exact Finset.sum_congr rfl fun x _ => gradNormSq_eq_gradNormIn_sq_general _ _ x
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal U.latticeVolume⁻¹ * ∫⁻ ω, ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2) ∂μ
        ≤ ENNReal.ofReal U.latticeVolume⁻¹ * ENNReal.ofReal (CE * Q * U.latticeVolume *
            U.latticeVolume ^ (1 / ((2 * d : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hEn U q) zero_le
      _ = ENNReal.ofReal (CE * Q * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hvol0.le)]
          congr 1
          have hr : U.latticeVolume ^ (1 / ((2 * d : ℕ) : ℝ)) =
              (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) := by
            rw [hvol]
            exact three_pow_pow_rpow_inv_two_mul hd0 (n + 1)
          rw [hr, show U.latticeVolume⁻¹ * (CE * Q * U.latticeVolume *
              (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) = CE * Q * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) *
              (U.latticeVolume⁻¹ * U.latticeVolume) by ring, inv_mul_cancel₀ hvne, mul_one]
      _ ≤ ENNReal.ofReal (CE * (K * Q) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : CE * Q ≤ CE * (K * Q) := mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left hQ0 hK1) hCE
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hne : ∀ k ≤ n + 1, (U.subcubesAt k).Nonempty := fun k hk => by
    rw [← Finset.card_pos, hU, card_subcubesAt_eq_general hk,
      Rigidity.Proofs.Multiscale.card_centers hk]
    positivity
  -- the term of Lemma 5.7 around the local matrices
  set B : ℕ → Configuration d → ℝ := fun k ω => (((U.subcubesAt k).card : ℝ))⁻¹ *
    ∑ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeMuGradAvg ω V q j - ξ j) ^ 2 with hBdef
  set W : ℕ → Configuration d → ℝ := fun k ω => (((U.subcubesAt k).card : ℝ))⁻¹ *
    ∑ V ∈ U.subcubesAt k, ∑ j : Fin d,
      (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p k *ᵥ q) j) ^ 2 with hWdef
  set Dk : ℕ → ℝ := fun k => ∑ j : Fin d, ((cubeAhomInvFinite p k *ᵥ q) j - ξ j) ^ 2 with hDk
  have hBW : ∀ k ∈ s, ∀ ω, B k ω ≤ 2 * W k ω + 2 * Dk k := by
    intro k hk ω
    have hcard : (0 : ℝ) < (U.subcubesAt k).card := by
      exact_mod_cast (hne k (Finset.mem_Ico.1 hk).2.le).card_pos
    have hpt : ∀ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeMuGradAvg ω V q j - ξ j) ^ 2 ≤
        2 * ∑ j : Fin d, (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p k *ᵥ q) j) ^ 2 +
          2 * Dk k := by
      intro V _
      rw [hDk, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      nlinarith [sq_nonneg (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p k *ᵥ q) j -
        ((cubeAhomInvFinite p k *ᵥ q) j - ξ j))]
    have hs1 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hs1
    simp only [hBdef, hWdef]
    have h2 := mul_le_mul_of_nonneg_left hs1 (inv_nonneg.2 hcard.le)
    have e : (((U.subcubesAt k).card : ℝ))⁻¹ * (2 * ∑ V ∈ U.subcubesAt k, ∑ j : Fin d,
        (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p k *ᵥ q) j) ^ 2 +
          ((U.subcubesAt k).card : ℝ) * (2 * Dk k)) =
        2 * ((((U.subcubesAt k).card : ℝ))⁻¹ * ∑ V ∈ U.subcubesAt k, ∑ j : Fin d,
          (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p k *ᵥ q) j) ^ 2) + 2 * Dk k := by
      field_simp
    linarith
  have hW0 : ∀ k ∈ s, ∀ ω, 0 ≤ W k ω := fun k _ ω =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB0 : ∀ k ∈ s, ∀ ω, 0 ≤ B k ω := fun k _ ω =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA0 : ∀ k ∈ s, ∀ ω, 0 ≤ cubeMuRestrictError ω U k q := fun k _ ω =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have mW : ∀ k ∈ s, AEMeasurable (W k) μ := fun k _ =>
    (Finset.aemeasurable_fun_sum _ fun V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      (((measurable_cubeMuGradAvg hd0 V q j).sub_const _).pow_const 2).aemeasurable).const_mul _
  have mA : ∀ k ∈ s, AEMeasurable (fun ω => cubeMuRestrictError ω U k q) μ := fun k hk =>
    aemeasurable_cubeMuRestrictError hd0 (show k ≤ n + 1 from (Finset.mem_Ico.1 hk).2.le) q
  set T : ℕ → ℝ := fun k => ∑ l ∈ Finset.Ico k (n + 1), cubeTau (d := d) p l with hTdef
  have IW : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal (W k ω) ∂μ ≤
      ENNReal.ofReal (C57 * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k hk
    refine lintegral_ofReal_avg_le (hne k (Finset.mem_Ico.1 hk).2.le)
      (fun V _ ω => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (fun V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
        (((measurable_cubeMuGradAvg hd0 V q j).sub_const _).pow_const 2).aemeasurable)
      fun V hV => ?_
    have h := h57 V q
    rw [TriadicCube.scale_of_mem_subcubesAt hV] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hτk : cubeTau (d := d) p k ≤ T k :=
      Finset.single_le_sum (f := fun l => cubeTau (d := d) p l) (fun l _ => cubeTau_nonneg p l)
        (Finset.mem_Ico.2 ⟨le_rfl, (Finset.mem_Ico.1 hk).2⟩)
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC57 hQ0)
  have hDkb : ∀ k ∈ s, Dk k ≤ CS * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hk).2
    exact hrate k n hkn q
  have If : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal (cubeMuRestrictError ω U k q + B k ω) ∂μ ≤
      ENNReal.ofReal (Cf * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    obtain ⟨h3, h4⟩ := hks k h1 h2
    have hA := h55 k (n + 1) q h3 h2 h4
    rw [← three_rpow_neg_div_four_eq] at hA
    have hpt : ∀ ω, ENNReal.ofReal (cubeMuRestrictError ω U k q + B k ω) ≤
        ENNReal.ofReal (cubeMuRestrictError ω U k q) + (ENNReal.ofReal 2 * ENNReal.ofReal (W k ω) +
          ENNReal.ofReal (2 * Dk k)) := by
      intro ω
      have hDk0 : 0 ≤ Dk k := Finset.sum_nonneg fun j _ => sq_nonneg _
      have h2W : 0 ≤ 2 * W k ω := mul_nonneg (by norm_num) (hW0 k hk ω)
      have h2D : 0 ≤ 2 * Dk k := mul_nonneg (by norm_num) hDk0
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_add h2W h2D,
        ← ENNReal.ofReal_add (hA0 k hk ω) (add_nonneg h2W h2D)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [hBW k hk ω]
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_left' (mA k hk).ennreal_ofReal, lintegral_add_left'
      (((mW k hk).ennreal_ofReal).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const, measure_univ, mul_one]
    refine (add_le_add hA (add_le_add (mul_le_mul_of_nonneg_left (IW k hk) zero_le)
      le_rfl)).trans ?_
    have hDk0 : 0 ≤ Dk k := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hTk0 : 0 ≤ T k + (3 : ℝ) ^ (-(k : ℝ) / 4) :=
      add_nonneg (Finset.sum_nonneg fun l _ => cubeTau_nonneg p l) (by positivity)
    have hX0 : 0 ≤ 2 * (C57 * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC57 hQ0) hTk0)
    have h2D : 0 ≤ 2 * Dk k := mul_nonneg (by norm_num) hDk0
    have hA' : 0 ≤ C55 * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4)) :=
      mul_nonneg (mul_nonneg hC55 hQ0) hTk0
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_add hX0 h2D,
      ← ENNReal.ofReal_add hA' (add_nonneg hX0 h2D)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hD := hDkb k hk
    rw [hCf]
    nlinarith
  have hf : ∀ k ∈ s, ∀ ω, 0 ≤ cubeMuRestrictError ω U k q + B k ω := fun k hk ω =>
    add_nonneg (hA0 k hk ω) (hB0 k hk ω)
  have mf : ∀ k ∈ s, AEMeasurable (fun ω => cubeMuRestrictError ω U k q + B k ω) μ := fun k hk =>
    (mA k hk).add ((Finset.aemeasurable_fun_sum _ fun V _ => Finset.aemeasurable_fun_sum _
      fun j _ => (((measurable_cubeMuGradAvg hd0 V q j).sub_const _).pow_const
        2).aemeasurable).const_mul _)
  have hmain := lintegral_ofReal_le_of_le (μ := μ)
    (X := fun ω => cubeFlatnessError U (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
      (partitionAnchor ω x)) ξ)
    (f₀ := fun ω => cubeCoarseEnergy ω U (cubeMuMinimizer ω U q))
    (f := fun k ω => cubeMuRestrictError ω U k q + B k ω)
    (g := fun _ _ => 0)
    (s := s) (a₀ := CM * (3 : ℝ) ^ (2 * n₀))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (3 : ℝ) ^ (2 * n₀) * Ξ₂ + ∑ k ∈ s, CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
      (3 * ∑ j : Fin d, (ξ j - ξ j) ^ 2 + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ₂))
    (b₀ := CE * (K * Q) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2))
    (bf := fun k => Cf * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => 0 * (K * Q) / 3 ^ k)
    (by positivity) (fun k _ => by positivity)
    (add_nonneg (mul_nonneg (by positivity) hΞ₂0) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun j _ => sq_nonneg _)) (mul_nonneg (by positivity) hΞ₂0))))
    (fun ω => cubeCoarseEnergy_nonneg _ _) hf (fun k _ ω => le_rfl)
    (aemeasurable_cubeCoarseEnergy_cubeMuMinimizer hd0 U q) mf (fun k _ => aemeasurable_const)
    (fun ω => by
      have h := hpw (n + 1) n₀ hn₀2 hn₀m ω q ξ (fun _ => ξ)
      simp only [add_zero]
      exact h)
    I₀ If (fun k _ => by simp) (mul_nonneg (mul_nonneg hCE (mul_nonneg hK0 hQ0)) (by positivity))
    (fun k _ => mul_nonneg (mul_nonneg hCf0 hQ0)
      (add_nonneg (Finset.sum_nonneg fun l _ => cubeTau_nonneg p l) (by positivity)))
    (fun k _ => by simp)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact cubeNuFlatness_arith (τ := cubeTau (d := d) p) (cubeTau_nonneg p) hCM hCE hCf0 le_rfl hK0
    hL0 hQ0 hΞ₂0 hΞ₂K le_rfl (three_pow_mul_rpow_le_of_le hn₀E)
    (Zc := fun _ => ∑ j : Fin d, (ξ j - ξ j) ^ 2) fun k => by simp

end Expectation

end Rigidity.Percolation
