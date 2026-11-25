import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralTileSums
import PercolationClusterHomogenization.Proofs.Dirichlet.BlockGeometry
import PercolationClusterHomogenization.Proofs.Dirichlet.ChainSums

/-!
# The error chain of Section 6 in every dimension

Lemmas 6.2 and 6.3 and Proposition 6.1 of Armstrong and Dario combined, in every dimension
`d ≥ 2`, with the mesoscopic cubes of side `3^{2k}` for the `μ` test, the tiles of side `K = 3^k`
for the maximizers of `ν`, the layer depth `r = 3^{4k}`, the cutoff width `ρ = 3^{3k}` and the
block of `blockGeometry`: for `u` harmonic on `C_*(□_m)` at the vertices whose lattice neighbours
lie in `□_m` and the homogenized solution `u_h`,
`Σ_{C_*(□_m)} (u − u_h)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃`, with the errors `δ₁, δ₂, δ₃` explicit in the
sums `S₂ = Σ_{edges in □_m} |∇w̃|²` and `S_t = Σ_{edges in □_m} |∇w̃|^t` of the datum
(`cube_error_chain`). The planar form is `planar_error_chain`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The Poincaré constant of `□_m` in the error chain. -/
noncomputable def cubeChainP (d : ℕ) (K₀ : ℝ) (m k₀ : ℕ) : ℝ :=
  (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
    ((3 : ℝ) ^ (m + 1)) ^ 2

/-- The Poincaré constant of the tiles in the error chain. -/
noncomputable def cubeChainPT (d : ℕ) (K₀ : ℝ) (k k₀ : ℕ) : ℝ :=
  (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
    ((3 : ℝ) ^ (k + 1)) ^ 2

theorem three_pow_div_three_pow_sub_one_nonneg (d : ℕ) : (0 : ℝ) ≤ 3 ^ d / (3 ^ d - 1) := by
  have h : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  exact div_nonneg (by positivity) (by linarith)

theorem cubeChainP_nonneg (d : ℕ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (m k₀ : ℕ) :
    0 ≤ cubeChainP d K₀ m k₀ := by
  have := three_pow_div_three_pow_sub_one_nonneg d
  unfold cubeChainP
  positivity

theorem cubeChainPT_nonneg (d : ℕ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (k k₀ : ℕ) :
    0 ≤ cubeChainPT d K₀ k k₀ := by
  have := three_pow_div_three_pow_sub_one_nonneg d
  unfold cubeChainPT
  positivity

/-- The error `δ₁` of Lemma 6.2 in the error chain, for the sums `S₂`, `S_t`. -/
noncomputable def cubeChainDeltaOne (d : ℕ) (σ ε t : ℝ) (m k : ℕ) (S2 St : ℝ) : ℝ :=
  2 * ((ε * σ ^ 2 + σ * (1 - ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ d /
        ((3 ^ (2 * k) : ℕ) : ℝ) ^ d) / 2 +
      σ * (√(1 / ((3 ^ (2 * k) : ℕ) : ℝ)) +
        √(1 - ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ d /
          ((3 ^ (2 * k) : ℕ) : ℝ) ^ d) + √(1 / ((3 ^ k : ℕ) : ℝ)))) * S2) +
    2 * (σ / √((3 ^ (2 * k) : ℕ) : ℝ) * S2) +
    ((3 ^ m : ℕ) : ℝ) ^ d *
      (σ * ((2 * d * ((3 ^ (4 * k) + 1 + 3 ^ (2 * k) : ℕ) : ℝ) / ((3 ^ m : ℕ) : ℝ)) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) *
          ((1 + (3 : ℝ) ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t *
            (((3 ^ (2 * k) : ℕ) : ℝ) / ((3 ^ (4 * k) : ℕ) : ℝ)) ^ t)) * St) /
          ((3 ^ m : ℕ) : ℝ) ^ d) ^ (2 / t)))

/-- The error `δ₂` of Lemma 6.3 in the error chain. -/
noncomputable def cubeChainDeltaTwo (d : ℕ) (σ ε γ t K₀ CA : ℝ) (m k k₀ : ℕ) (S2 St : ℝ) : ℝ :=
  (6 * ((3 ^ k : ℕ) : ℝ) ^ d * ((ε + d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ)) *
      (S2 / ((3 ^ k : ℕ) : ℝ) ^ d)) +
    3 * (max σ 1 * ((d : ℝ) * (3 * ((1 + (d : ℝ)) * 2 ^ d * ((3 ^ k : ℕ) : ℝ) ^ 3 *
      (10 * (d : ℝ) * max σ 1 / (σ * (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2)) +
        1 / ((3 ^ k : ℕ) : ℝ)) * S2))) +
    6 * max σ 1 * ((d : ℝ) * (1 / ((3 ^ (3 * k) : ℕ) : ℝ)) ^ 2) *
      (cubeChainPT d K₀ k k₀ * (4 * S2) +
        CA * ((3 ^ k : ℕ) : ℝ) ^ 4 / (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2 * S2)) +
  ((3 ^ m : ℕ) : ℝ) ^ d *
    ((2 + 3 * max σ 1 / σ) *
      (2 * (σ * ((2 * d * ((3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k + 1 : ℕ) : ℝ) /
          ((3 ^ m : ℕ) : ℝ)) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) * (St / ((3 ^ m : ℕ) : ℝ) ^ d)) ^ (2 / t))) +
        88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
          ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
          ((((3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k : ℕ) : ℝ) + 1) /
            ((3 ^ m : ℕ) : ℝ)) ^ γ *
          ((d : ℝ) ^ (t / 2 - 1) * (St / ((3 ^ m : ℕ) : ℝ) ^ d)) ^ (2 / t)))

/-- The `L²` error `δ₃` of Lemma 6.3 (iii) in the error chain. -/
noncomputable def cubeChainDeltaThree (d : ℕ) (σ K₀ C₃ : ℝ) (k k₀ : ℕ) (S2 : ℝ) : ℝ :=
  2 * (cubeChainPT d K₀ k k₀ * (4 * S2)) +
    2 * (C₃ * ((3 ^ k : ℕ) : ℝ) ^ 4 / (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2 * (σ / σ * S2))

/-- **The error chain of Section 6** in every dimension `d ≥ 2`. -/
theorem cube_error_chain (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K₀ C₃ CA : ℝ, 0 ≤ K₀ ∧ 0 ≤ C₃ ∧ 0 ≤ CA ∧
    ∀ (ω : Configuration d) (hP : PartitionEvent ω) (m k k₀ : ℕ), k₀ ≤ k →
      2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k ≤ 3 ^ m →
      (∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k₀) →
      ∀ (hU : PartitionResolved ω ⟨m, 0⟩) {ε : ℝ}, 0 ≤ ε →
      (∀ T : TriadicCube d, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices →
        ∀ q : Fin d → ℝ, |(∑ j, q j ^ 2 / σ) / 2 + cubeMu ω T q| ≤ ε * ∑ j, q j ^ 2) →
      (∀ T : TriadicCube d, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices →
        ∀ ξ : Fin d → ℝ, |cubeNu ω T ξ - σ * (∑ j, ξ j ^ 2) / 2| ≤ ε * ∑ j, ξ j ^ 2) →
      ∀ {γ t : ℝ}, 0 < γ → γ ≤ 1 / 16 → 2 < t → γ * (t / (t - 2)) < 1 →
      ∀ u : Vertex d → ℝ,
      (fun x : ↥(crossingClusterVertices ω ⟨m, 0⟩) => u x) ∈ cubeHarmonic ω ⟨m, 0⟩ →
      ∑ x ∈ crossingClusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube)
          (cubeDatum (by omega) hP m hU u) x) ^ 2 ≤
        2 * (cubeChainP d K₀ m k₀ *
          ((cubeChainDeltaOne d σ ε t m k
              (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube
                (cubeDatum (by omega) hP m hU u))
              (innerRpowSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube
                (cubeDatum (by omega) hP m hU u) t) +
            cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀
              (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube
                (cubeDatum (by omega) hP m hU u))
              (innerRpowSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube
                (cubeDatum (by omega) hP m hU u) t)) / 1)) +
        2 * cubeChainDeltaThree d σ K₀ C₃ k k₀
          (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube
            (cubeDatum (by omega) hP m hU u)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_cube_sum_sq_le_of_eq_zero hd
  obtain ⟨C₃, hC₃, h3⟩ := exists_sum_sq_patch_sub_le_inner (d := d) hd0 (fun _ => σ)
    hσ (fun _ => ⟨le_rfl, le_rfl⟩)
  obtain ⟨CA, hCA, hA⟩ := cube_exists_sum_tiles_sq_dirichletSolution_sub_le hd0 hσ
  refine ⟨K₀, C₃, CA, hK₀0, hC₃, hCA, ?_⟩
  intro ω hP m k k₀ hk₀k hbig hk₀ hU ε hε0 hμ hν γ t hγ0 hγ ht hγt u hu
  set w := cubeDatum hd0 hP m hU u with hw
  obtain ⟨hsub, hT1, hT2⟩ := blockGeometry (d := d) (m := m) (k := k) (r := 3 ^ (4 * k)) hbig
  have hdiv := blockCorner_dvd (d := d) m k (3 ^ (4 * k))
  have hkm : k + 1 ≤ m := by
    have h1 : 3 ^ (k + 1) ≤ 3 ^ m := by
      have : 3 ^ (k + 1) ≤ 2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k := by
        rw [pow_succ]
        have : 3 ^ k ≤ 3 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hk₀m : k₀ ≤ m := by omega
  have hkU : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k₀ :=
    fun x hx => hk₀ x (origin_vertices_subset_succ' m hx)
  have hkUk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k :=
    fun x hx => (hkU x hx).trans hk₀k
  have hsz : (⟨m, 0⟩ : TriadicCube d).toIntegerCube.size = 3 ^ m := rfl
  have hV : (0 : ℝ) < ((3 ^ m : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((3 ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (by norm_num : 0 < 3) m
    exact pow_pos this d
  have h62 := cube_lemmaSixTwo (n := 2 * k) (r := 3 ^ (4 * k)) hd0 hP (by omega) (by omega)
    (by positivity) hU hkUk hσ hε0 hμ hu ht.le
  rw [hsz] at h62
  have h₁ : innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) ≤
      innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube u +
        cubeChainDeltaOne d σ ε t m k
          (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube w)
          (innerRpowSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube w t) := by
    refine (le_add_mul_of_div_le hV h62).trans_eq ?_
    simp only [cubeChainDeltaOne, innerSqSum, innerRpowSum]
    ring
  have h63 := cube_lemmaSixThree (ρ := 3 ^ (3 * k)) hd0 hP hkUk hσ w
    (by positivity) hdiv (blockCount m k (3 ^ (4 * k))) hsub hT1 hT2 (by positivity) hγ0 hγ ht hγt
  rw [hsz] at h63
  have h63' := le_add_add_mul_of_div_le hV h63
  have hS2uh := innerSqSum_dirichletSolution_le hd0 hσ (⟨m, 0⟩ : TriadicCube d).toIntegerCube w
  have htile := cube_sum_tileError_le hd0 hP hk₀k hU hkU hε0 hν hdiv
    (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) hsub
  have hpatch := sum_sq_cubeTilePatch_tiles_le hd0 hK₀0 hK₀ hP hk₀k hkm hkU hdiv
    (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) hsub
  have haff := hA (⟨m, 0⟩ : TriadicCube d).toIntegerCube w (3 ^ (4 * k))
    (by positivity) (blockCorner m k (3 ^ (4 * k))) (blockCount m k (3 ^ (4 * k))) (3 ^ k)
    (by positivity) hsub
  have hlay := cube_layer_energy_div_le (⟨m, 0⟩ : TriadicCube d).toIntegerCube
    (by rw [hsz]; positivity) w hσ.le
    (3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k + 1) ht.le
  have hhardy := cube_hardy_term_le (⟨m, 0⟩ : TriadicCube d).toIntegerCube w ht.le
  rw [hsz] at hlay hhardy
  have hγt' : 0 < 1 - γ * (t / (t - 2)) := by linarith
  have hPT := cubeChainPT_nonneg d hK₀0 k k₀
  have h₂ : innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (patch (cubeCutoff (cornerCube (blockCorner m k (3 ^ (4 * k)))
            (blockCount m k (3 ^ (4 * k)) * 3 ^ k)) (3 ^ (3 * k)))
          (cubeTilePatch ω k (blockCorner m k (3 ^ (4 * k)))
            (dirichletSolution (constCond fun _ => σ)
              (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w))
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w)) ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) +
        cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀
          (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube w)
          (innerRpowSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube w t) := by
    refine h63'.trans (add_le_add le_rfl ?_)
    unfold cubeChainDeltaTwo
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hV.le)
    · refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_left (htile.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hS2uh (by positivity)) (by positivity))) (by positivity)
      · gcongr
        exact hS2uh
      · refine mul_le_mul_of_nonneg_left (add_le_add ?_ haff) (by positivity)
        exact hpatch.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hS2uh (by norm_num)) hPT)
    · refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hlay (by norm_num))
        (mul_le_mul_of_nonneg_left hhardy ?_)) (by positivity)
      have h1 : 0 ≤ ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
        Real.rpow_nonneg (div_nonneg (by positivity) hγt'.le) _
      positivity
  have h3' := h3 (⟨m, 0⟩ : TriadicCube d).toIntegerCube w (3 ^ (4 * k))
    (by positivity) (blockCorner m k (3 ^ (4 * k))) (blockCount m k (3 ^ (4 * k))) (3 ^ k)
    (by positivity) hsub (3 ^ (3 * k)) (crossingClusterVertices ω ⟨m, 0⟩)
    (Finset.filter_subset _ _)
    (cubeTilePatch ω k (blockCorner m k (3 ^ (4 * k))) (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w))
  have h₃ := h3'.trans (show _ ≤ cubeChainDeltaThree d σ K₀ C₃ k k₀
      (innerSqSum (⟨m, 0⟩ : TriadicCube d).toIntegerCube w) by
    unfold cubeChainDeltaThree
    exact add_le_add (mul_le_mul_of_nonneg_left (hpatch.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS2uh (by norm_num)) hPT))
      (by norm_num)) le_rfl)
  have hv : ∀ x, x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube →
      patch (cubeCutoff (cornerCube (blockCorner m k (3 ^ (4 * k)))
          (blockCount m k (3 ^ (4 * k)) * 3 ^ k)) (3 ^ (3 * k)))
        (cubeTilePatch ω k (blockCorner m k (3 ^ (4 * k)))
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w))
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) x =
      dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w x := by
    intro x hx
    refine patch_cubeCutoff_of_not_mem _ _ _ _ fun hxT => hx ?_
    refine shrinkCube_one_vertices_subset_cubeInterior _ (shrinkCube_vertices_mono _
      (show 1 ≤ 3 ^ (4 * k) + 3 from le_trans (by norm_num) (Nat.le_add_left 3 _))
      (hsub (cornerCube_mul_subset_succ _ _ _ hxT)))
  exact cube_sum_sq_sub_uhom_le hd0 hK₀0 hK₀ hP hk₀m hk₀ hU hu hv h₁ h₂ h₃

end Rigidity.Dirichlet
