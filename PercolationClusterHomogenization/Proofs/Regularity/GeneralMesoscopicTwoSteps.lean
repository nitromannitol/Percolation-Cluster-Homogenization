import PercolationClusterHomogenization.Proofs.Regularity.GeneralQuadraticLipschitz
import PercolationClusterHomogenization.Proofs.Regularity.GeneralLatticeMeanValue
import PercolationClusterHomogenization.Proofs.Regularity.GeneralLatticeKIterationTwo

/-!
# Steps of the proof of Lemma 7.3 at `k = 2` in every dimension

The steps of the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2) which pass between
`u` on the infinite cluster `C` of a configuration of `ℤᵈ` and its coarsening
`U = [u]_𝒫` (`partitionCoarse`) on the balls of `ℤᵈ`, with `D̃_k(r)` the excess of `u` over the
harmonic polynomials of degree `k` in the normalization `r^{-d/2} ‖·‖_{ℓ²(C ∩ B_r)}`
(`clusterBallVolumeL2`) and `D_k(r)` the excess of `U` on the lattice ball:

* `clusterExcess_two_leD`, `clusterExcess_zero_leD` (Step 1, (7.21)):
  `D̃_k(r) ≤ ‖u - U‖_r + 5^d D_k(r)`, the lattice harmonic quadratic functions restricting to
  harmonic quadratic polynomials of the cluster;
* `componentBallL2_coarse_sub_quad_leD` (the passage from (7.19) to (7.20) through (7.11), and
  Step 2, (7.22)–(7.23), at the top scale `T`): for a lattice harmonic function `v` on `B_{4T}`
  and a harmonic quadratic polynomial `W`,
  `‖U - W‖_{L̲²(B_T)} ≤ C ‖U - v‖_{L̲²(B_{4T})} + C T^{-d} ∑_{B_{4T}} |U - W|`, by the
  `ℓ^∞`–`ℓ¹` bound of lattice harmonic functions applied to `v - W`.

These are the planar statements of `PlanarMesoscopicTwoSteps` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

theorem clusterBallVolumeL2_nonnegD (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) :
    0 ≤ clusterBallVolumeL2 C r f :=
  Real.sqrt_nonneg _

/-- **Step 1 at `k = 2`.** -/
theorem clusterExcess_two_leD [NeZero d] (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {r : ℝ} (hr : 1 ≤ r) :
    (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
      clusterBallVolumeL2 (uniqueInfiniteComponent h) r
          (u - fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) +
        5 ^ d * ballExcess (componentBallSeminorm (latticeComponent d) 0)
          (latticeHarmonicQuadratic d) r
          (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) := by
  apply le_add_mul_iInf (by positivity)
  rintro ⟨wl, hwl⟩
  obtain ⟨a, p, M, hwl', hmem⟩ :=
    mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadraticD (uniqueInfiniteComponent h) hwl
  set w : uniqueInfiniteComponent h → ℝ := fun x => latticeQuadFunD a p M x.val with hw
  set U : Vertex d → ℝ := partitionCoarse (uniqueInfiniteComponent h) u with hU
  have h1 := iInf_le_of_le (f := fun w : clusterHarmonicQuadratic (uniqueInfiniteComponent h) =>
    clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w))
    (fun _ => clusterBallVolumeL2_nonnegD _ _ _) ⟨w, hmem⟩
  have e : u - w = (u - fun x => U x.val) +
      fun x => (fun y => U y - latticeQuadFunD a p M y) x.val := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply, hw]; ring
  have h2 := clusterBallVolumeL2_triangle (uniqueInfiniteComponent h) (by linarith : (0 : ℝ) ≤ r)
    (u - fun x => U x.val) (fun x => (fun y => U y - latticeQuadFunD a p M y) x.val)
  have h3 := clusterBallVolumeL2_le_five_pow_lattice (uniqueInfiniteComponent h) hr
    (fun y => U y - latticeQuadFunD a p M y)
  have e2 : componentBallL2 (latticeComponent d) 0 r
      (fun x => (fun y => U y - latticeQuadFunD a p M y) x.val) =
      componentBallSeminorm (latticeComponent d) 0 r ((fun x => U x.val) - wl) := by
    rw [componentBallSeminorm_apply]
    congr 1
    funext x
    simp only [Pi.sub_apply, hwl' x]
  rw [e2] at h3
  calc (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w))
      ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w) := h1
    _ ≤ _ := by rw [e]; linarith

/-- **Step 1 at `k = 0`.** -/
theorem clusterExcess_zero_leD [NeZero d] (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {r : ℝ} (hr : 1 ≤ r) :
    (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a)) ≤
      clusterBallVolumeL2 (uniqueInfiniteComponent h) r
          (u - fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) +
        5 ^ d * ballExcess (componentBallSeminorm (latticeComponent d) 0)
          (clusterConstants (latticeComponent d))
          r (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) := by
  apply le_add_mul_iInf (by positivity)
  rintro ⟨wl, c, hc⟩
  set U : Vertex d → ℝ := partitionCoarse (uniqueInfiniteComponent h) u with hU
  have h1 := iInf_le_of_le (f := fun a : ℝ =>
    clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a))
    (fun _ => clusterBallVolumeL2_nonnegD _ _ _) c
  have e : (u - fun _ => c) = (u - fun x => U x.val) + fun x => (fun y => U y - c) x.val := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have h2 := clusterBallVolumeL2_triangle (uniqueInfiniteComponent h) (by linarith : (0 : ℝ) ≤ r)
    (u - fun x => U x.val) (fun x => (fun y => U y - c) x.val)
  have h3 := clusterBallVolumeL2_le_five_pow_lattice (uniqueInfiniteComponent h) hr
    (fun y => U y - c)
  have e2 : componentBallL2 (latticeComponent d) 0 r (fun x => (fun y => U y - c) x.val) =
      componentBallSeminorm (latticeComponent d) 0 r ((fun x => U x.val) - wl) := by
    rw [componentBallSeminorm_apply]
    congr 1
    funext x
    simp only [Pi.sub_apply, hc x]
  rw [e2] at h3
  calc (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a))
      ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => c) := h1
    _ ≤ _ := by rw [e]; linarith

/-- The radius factor on the balls of `ℤᵈ`. -/
theorem componentBallL2_lattice_leD [NeZero d] (f : latticeComponent d → ℝ) {s r : ℝ}
    (hs : 6 * Real.sqrt d ≤ s) (hsr : s ≤ r) :
    componentBallL2 (latticeComponent d) 0 s f ≤
      Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (r / s) ^ ((d : ℝ) / 2) *
        componentBallL2 (latticeComponent d) 0 r f := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hvol := clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent d) 0 r
    hd one_pos (clusterCubeDensity_latticeComponent 0 (24 * Real.sqrt d) 1)
  have hX : (0 : ℝ) < 6 * Real.sqrt d * max 1 1 := by
    have := Real.sqrt_pos.2 (Nat.cast_pos.2 hd); positivity
  have hmono := radiusMonotone_componentBallSeminorm (latticeComponent d) 0 hX (by positivity)
    hvol f s r (by rw [max_self, mul_one]; exact hs) hsr le_rfl
  rw [componentBallSeminorm_apply, componentBallSeminorm_apply] at hmono
  exact hmono

/-- `∑ |f| ≤ (card) ‖f‖_{L̲²}` on a cluster ball. -/
theorem sum_abs_le_card_mul_componentBallL2D (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (f : C → ℝ) :
    ∑ x ∈ componentEuclideanBall C z r, |f x| ≤
      ((componentEuclideanBall C z r).card : ℝ) * componentBallL2 C z r f := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := componentEuclideanBall C z r)
    (f := fun x => |f x|)
  simp only [sq_abs] at hcs
  rw [sum_sq_eq_card_mul_componentBallL2_sq] at hcs
  set n := ((componentEuclideanBall C z r).card : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hN0 := componentBallL2_nonneg C z r f
  have h0 : 0 ≤ ∑ x ∈ componentEuclideanBall C z r, |f x| := sum_nonneg fun _ _ => abs_nonneg _
  have hsq : (∑ x ∈ componentEuclideanBall C z r, |f x|) ^ 2 ≤
      (n * componentBallL2 C z r f) ^ 2 := by
    rw [mul_pow]; nlinarith
  nlinarith [mul_nonneg hn0 hN0]

/-- The constant of Step 2 at the top scale. -/
noncomputable def coarseTopConstD (d : ℕ) : ℝ :=
  Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (4 : ℝ) ^ ((d : ℝ) / 2) +
    meanValueConst d * (2 * Real.sqrt d) ^ d * 9 ^ d

theorem coarseTopConstD_nonneg (d : ℕ) : 0 ≤ coarseTopConstD d := by
  have := meanValueConst_nonneg d
  unfold coarseTopConstD; positivity

/-- **Step 2 at the top scale.** For `v` lattice harmonic on `B_{4T}` and `W = a + ⟪p, ·⟫ + q_M`
with `tr M = 0`, `‖U - W‖_{L̲²(B_T)} ≤ C ‖U - v‖_{L̲²(B_{4T})} + C_MV T^{-d} ∑_{B_{4T}} |U - W|`. -/
theorem componentBallL2_coarse_sub_quad_leD [NeZero d] (U : Vertex d → ℝ) {T : ℝ}
    (hTm : meanValueScale d ≤ T) (hT6 : 6 * Real.sqrt d ≤ T) (hT3 : 3 ≤ T)
    {v : latticeComponent d → ℝ} (hv : v ∈ latticeHarmonicClass 0 (4 * T)) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.trace = 0) :
    componentBallL2 (latticeComponent d) 0 T
        (fun x => U x.val - latticeQuadFunD a p M x.val) ≤
      coarseTopConstD d * componentBallL2 (latticeComponent d) 0 (4 * T)
          ((fun x : latticeComponent d => U x.val) - v) +
        meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d *
          ∑ y ∈ latticeBallPointsD 0 (4 * T), |U y - latticeQuadFunD a p M y| := by
  classical
  obtain ⟨F, hvF, hF⟩ := hv
  have hT0 : 0 < T := by linarith
  set N₄ := componentBallL2 (latticeComponent d) 0 (4 * T)
    ((fun x : latticeComponent d => U x.val) - v) with hN₄
  have hN₄0 : 0 ≤ N₄ := componentBallL2_nonneg _ _ _ _
  -- the triangle inequality
  have e : (fun x : latticeComponent d => U x.val - latticeQuadFunD a p M x.val) =
      ((fun x : latticeComponent d => U x.val) - v) +
        fun x => F x.val - latticeQuadFunD a p M x.val := by
    funext x
    show U x.val - latticeQuadFunD a p M x.val =
      (U x.val - v x) + (F x.val - latticeQuadFunD a p M x.val)
    rw [hvF x]; ring
  have htri := map_add_le_add (componentBallSeminorm (latticeComponent d) 0 T)
    ((fun x : latticeComponent d => U x.val) - v) (fun x => F x.val - latticeQuadFunD a p M x.val)
  rw [← e, componentBallSeminorm_apply, componentBallSeminorm_apply,
    componentBallSeminorm_apply] at htri
  -- the first term
  have h1 := componentBallL2_lattice_leD ((fun x : latticeComponent d => U x.val) - v) hT6
    (by linarith : T ≤ 4 * T)
  have e4 : 4 * T / T = 4 := by field_simp
  rw [e4] at h1
  -- the second term
  have hg : ∀ y : Fin d → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding 0) <
      4 * T → latticeLaplacian (fun y => F y - latticeQuadFunD a p M y) y = 0 := by
    intro y hy
    rw [latticeLaplacian_sub, hF y hy, latticeLaplacian_latticeQuadFunD, hM, mul_zero, sub_zero]
  have h2 := componentBallL2_le_sum_abs_of_latticeHarmonicD
    (fun y => F y - latticeQuadFunD a p M y) 0 hTm hg
  have hpt : ∀ x : latticeComponent d, |F x.val - latticeQuadFunD a p M x.val| ≤
      |((fun x : latticeComponent d => U x.val) - v) x| +
        |U x.val - latticeQuadFunD a p M x.val| := fun x => by
    have : F x.val - latticeQuadFunD a p M x.val =
        -((fun x : latticeComponent d => U x.val) - v) x +
          (U x.val - latticeQuadFunD a p M x.val) := by
      show F x.val - latticeQuadFunD a p M x.val = -(U x.val - v x) +
        (U x.val - latticeQuadFunD a p M x.val)
      rw [hvF x]; ring
    rw [this]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have hs1 : ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 (4 * T),
      |F x.val - latticeQuadFunD a p M x.val| ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 (4 * T),
          |((fun x : latticeComponent d => U x.val) - v) x| +
        ∑ y ∈ latticeBallPointsD 0 (4 * T), |U y - latticeQuadFunD a p M y| := by
    rw [← sum_latticeBallPointsD 0 (4 * T) (fun y => |U y - latticeQuadFunD a p M y|),
      ← sum_add_distrib]
    exact sum_le_sum fun x _ => hpt x
  have hS1 := sum_abs_le_card_mul_componentBallL2D (latticeComponent d) 0 (4 * T)
    ((fun x : latticeComponent d => U x.val) - v)
  have hncard : ((componentEuclideanBall (latticeComponent d) 0 (4 * T)).card : ℝ) ≤
      9 ^ d * T ^ d := by
    have := card_componentEuclideanBall_le (latticeComponent d) 0 (by linarith : (0 : ℝ) ≤ 4 * T)
    calc _ ≤ (2 * (4 * T) + 3) ^ d := this
      _ ≤ (9 * T) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
      _ = 9 ^ d * T ^ d := mul_pow _ _ _
  set S₂ := ∑ y ∈ latticeBallPointsD 0 (4 * T), |U y - latticeQuadFunD a p M y|
  have hsum : ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 (4 * T),
      |F x.val - latticeQuadFunD a p M x.val| ≤ 9 ^ d * T ^ d * N₄ + S₂ := by
    have := mul_le_mul_of_nonneg_right hncard hN₄0
    linarith
  have hCMV : 0 ≤ meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d := by
    have := meanValueConst_nonneg d; positivity
  have hfinal := h2.trans (mul_le_mul_of_nonneg_left hsum hCMV)
  have hT2 : meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d * (9 ^ d * T ^ d * N₄ + S₂) =
      meanValueConst d * (2 * Real.sqrt d) ^ d * 9 ^ d * N₄ +
        meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d * S₂ := by
    field_simp
  rw [hT2] at hfinal
  have hK : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) := Real.sqrt_nonneg _
  rw [coarseTopConstD]
  nlinarith

end Rigidity.Proofs.Regularity
