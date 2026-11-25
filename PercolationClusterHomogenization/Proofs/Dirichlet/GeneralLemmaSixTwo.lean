import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralInterpolation
import PercolationClusterHomogenization.Proofs.Dirichlet.GridTiles

/-!
# Lemma 6.2 of Armstrong and Dario in every dimension

Let `□_m` be a triadic cube of `ℤᵈ` resolved by the partition into good cubes, with all partition
cubes of its vertices of scale at most `k ≤ m`, let `u` be harmonic on `C_*(□_m)` at the vertices
whose lattice neighbours lie in `□_m`, `w̃` the boundary interpolation of the coarsened function
(`cubeDatum`) and `u_hom` the solution of the discrete Dirichlet problem for `ā = σ I` with datum
`w̃`. Suppose that `|μ(T, q) + |q|²/(2σ)| ≤ ε |q|²` for every triadic cube `T ⊆ □_m` of scale `k`.
Then, with `N = 3^n ≥ K = 3^k` and `M = N/K − 1`, at every translate `x + □` of side `N` away from
`∂□_m` the triadic cubes of scale `k` inside `x + □` starting at the first point of the triadic
grid of scale `k` after `x` form a block of `M^d` tiles on which `u` is tested in `μ`
(`cubeMu_le_test`), and `exists_mu_test_of_subcubes` gives the `μ` test of the lattice Lemma 6.2
at `x` (`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test`), with the errors summed by
`sum_subcube_errors_le`:
`L^{-d} E_ā(u_hom) ≤ L^{-d} E(u) + 2 (ε σ² + σ β/2 + σ γ + σ N^{-1/2}) L^{-d} Σ |∇w̃|²`
`+ (layer term)`
(`cube_lemmaSixTwo`). This is Lemma 6.2 of the source, in every dimension, with the discrete
homogenized solution and the triadic tiles in place of the translates of `□_n`; the planar form is
`planar_lemmaSixTwo`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The boundary vertices of the cluster of `□_m`. -/
noncomputable def cubeClusterBoundary (ω : Configuration d) (m : ℕ) : Finset (Vertex d) :=
  (crossingClusterVertices ω ⟨m, 0⟩).filter fun x =>
    x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube

theorem cubeClusterBoundary_subset (ω : Configuration d) (m : ℕ) :
    cubeClusterBoundary ω m ⊆ crossingClusterVertices ω ⟨m, 0⟩ := Finset.filter_subset _ _

/-- The datum `w̃` of the homogenized problem: `u` on `C_*(□_m) ∩ ∂□_m`, the coarsened function
elsewhere. -/
noncomputable def cubeDatum (hd : 0 < d) (hP : PartitionEvent ω) (m : ℕ)
    (hU : PartitionResolved ω ⟨m, 0⟩) (u : Vertex d → ℝ) : Vertex d → ℝ :=
  boundaryInterpolation (partitionCoarseData hd hP ⟨m, 0⟩ hU) (cubeClusterBoundary ω m) u

theorem cubeDatum_of_mem_cubeInterior (hd : 0 < d) (hP : PartitionEvent ω) {m : ℕ}
    (hU : PartitionResolved ω ⟨m, 0⟩) (u : Vertex d → ℝ) {y : Vertex d}
    (hy : y ∈ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) :
    cubeDatum hd hP m hU u y = u (partitionAnchor ω y) := by
  have hy' : y ∉ cubeClusterBoundary ω m := fun h => (Finset.mem_filter.1 h).2 hy
  unfold cubeDatum
  rw [boundaryInterpolation_of_not_mem _ _ hy']
  rfl

/-- **The `μ` test at a translate**, from the tests on its triadic tiles. -/
theorem exists_cube_mu_test (hd : 0 < d) (hP : PartitionEvent ω) {m n k r : ℕ} (hkn : k ≤ n)
    (hkm : k ≤ m) (hU : PartitionResolved ω ⟨m, 0⟩)
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k)
    {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω ⟨m, 0⟩) => u x) ∈ cubeHarmonic ω ⟨m, 0⟩)
    (a : Fin d → ℝ) {x : Vertex d}
    (hx : x ∈ (trimCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (3 ^ n)).vertices \
      cubeLayer (trimCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (3 ^ n)) (r + 1)) :
    ∃ μ : ℝ, μ ≤ (∑ y ∈ (cornerCube x (3 ^ n)).vertices, cubeEnergy ω ⟨m, 0⟩ u y) /
          ((3 ^ n : ℕ) : ℝ) ^ d / 2 -
        ∑ j, a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j *
          cubeEdgeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j ∧
      |(∑ j, (a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j) ^ 2 / a j) / 2 + μ| ≤
        (∑ i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices, ((3 ^ k : ℕ) : ℝ) ^ d *
          |(∑ j, (a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j) ^ 2 / a j) / 2 +
            cubeMu ω (gridTile k (triadicGridCorner k x) i)
              (fun j => a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j)|) /
            ((3 ^ n : ℕ) : ℝ) ^ d +
          |1 - ((cornerCube (0 : Vertex d) (3 ^ (n - k) - 1)).vertices.card : ℝ) *
            ((3 ^ k : ℕ) : ℝ) ^ d / ((3 ^ n : ℕ) : ℝ) ^ d| *
            |(∑ j, (a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j) ^ 2 / a j) / 2| +
          |∑ j, a j * cubeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j *
            (cubeEdgeSlope (3 ^ n) (cubeDatum hd hP m hU u) x j -
              (∑ i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices, ((3 ^ k : ℕ) : ℝ) ^ d *
                cubeEdgeSlope (3 ^ k) (cubeDatum hd hP m hU u)
                  (triadicGridCorner k x + ((3 ^ k : ℕ) : ℤ) • i) j) /
                ((3 ^ n : ℕ) : ℝ) ^ d)| := by
  set N := 3 ^ n
  set K := 3 ^ k
  set M := 3 ^ (n - k) - 1
  set z := triadicGridCorner k x
  set w := cubeDatum hd hP m hU u
  set p : Fin d → ℝ := fun j => cubeSlope N w x j
  have hV : (0 : ℝ) < ((N : ℕ) : ℝ) ^ d := by positivity
  have hW : (0 : ℝ) < ((K : ℕ) : ℝ) ^ d := by positivity
  have hdiv : ∀ t, (3 : ℤ) ^ k ∣ z t + (3 : ℤ) ^ k / 2 :=
    fun t => (triadicGridCorner_spec k x t).2.2
  set T : Vertex d → TriadicCube d := fun i => gridTile k z i
  have hTc : ∀ i, (T i).toIntegerCube = cornerCube (z + ((K : ℕ) : ℤ) • i) K :=
    fun i => gridTile_toIntegerCube hdiv i
  refine exists_mu_test_of_subcubes a p (fun j => cubeEdgeSlope N w x j) hV hW
    (cornerCube 0 M).vertices (fun i => cubeMu ω (T i) (fun j => a j * p j))
    (fun i => ∑ y ∈ (T i).toIntegerCube.vertices, cubeEnergy ω ⟨m, 0⟩ u y)
    (fun i j => cubeEdgeSlope K w (z + ((K : ℕ) : ℤ) • i) j) ?_ ?_
  · intro i hi
    obtain ⟨-, hint⟩ := gridTile_vertices_subset (r := r) hkn hx hi
    have hTU : (T i).vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices := fun y hy =>
      ((TriadicCube.mem_toIntegerCube_vertices _ y).1
        (Finset.filter_subset _ _ (hint y hy)))
    have hTres : PartitionResolved ω (T i) := fun y hy => hk y (hTU hy)
    have htest := cubeMu_le_test hd hP hTU hTres hkm hu (fun j => a j * p j)
    have hvol : (T i).latticeVolume = ((K : ℕ) : ℝ) ^ d := by
      change ((3 : ℝ) ^ k) ^ d = ((3 ^ k : ℕ) : ℝ) ^ d
      norm_cast
    rw [hvol] at htest
    have hG : ∀ j, (∑ y ∈ (T i).toIntegerCube.vertices,
        (if y + unit j ∈ (T i).toIntegerCube.vertices then
          u (partitionAnchor ω (y + unit j)) - u (partitionAnchor ω y) else 0)) /
          ((K : ℕ) : ℝ) ^ d = cubeEdgeSlope K w (z + ((K : ℕ) : ℤ) • i) j := by
      intro j
      unfold cubeEdgeSlope
      rw [← hTc i, Finset.sum_filter]
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      split_ifs with hyj
      · have hy' := (TriadicCube.mem_toIntegerCube_vertices _ y).1 hy
        have hyj' := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hyj
        rw [show w (y + unit j) = _ from cubeDatum_of_mem_cubeInterior hd hP hU u (hint _ hyj'),
          show w y = _ from cubeDatum_of_mem_cubeInterior hd hP hU u (hint y hy')]
      · rfl
    simp only [hG] at htest
    exact htest
  · have hblock : ∑ i ∈ (cornerCube 0 M).vertices,
        ∑ y ∈ (T i).toIntegerCube.vertices, cubeEnergy ω ⟨m, 0⟩ u y =
        ∑ y ∈ (cornerCube z (M * K)).vertices, cubeEnergy ω ⟨m, 0⟩ u y := by
      rw [sum_cornerCube_mul (by positivity) z M]
      exact Finset.sum_congr rfl fun i _ => by rw [hTc i]
    rw [hblock]
    have hMK : (M + 1) * K ≤ N := by
      change (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
    have hz : ∀ t, x t ≤ z t ∧ z t < x t + ((K : ℕ) : ℤ) := fun t => by
      have := triadicGridCorner_spec k x t
      exact ⟨this.1, by exact_mod_cast this.2.1⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (block_subset_cornerCube hMK hz)
      fun y _ _ => cubeEnergy_nonneg _ u y

/-- **Armstrong and Dario, Lemma 6.2**, in every dimension, with the discrete homogenized
solution for `ā = σ I` and the `μ` tests on the triadic tiles of scale `k`. -/
theorem cube_lemmaSixTwo (hd : 0 < d) (hP : PartitionEvent ω) {m n k r : ℕ} (hkn : k ≤ n)
    (hkm : k ≤ m) (hr : 0 < r) (hU : PartitionResolved ω ⟨m, 0⟩)
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k)
    {σ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 ≤ ε)
    (hconv : ∀ T : TriadicCube d, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices →
      ∀ q : Fin d → ℝ, |(∑ j, q j ^ 2 / σ) / 2 + cubeMu ω T q| ≤ ε * ∑ j, q j ^ 2)
    {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω ⟨m, 0⟩) => u x) ∈ cubeHarmonic ω ⟨m, 0⟩)
    {s : ℝ} (hs : 2 ≤ s) :
    innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u)) /
        (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d ≤
      (innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube u +
          2 * ((ε * σ ^ 2 + σ * (1 - ((((3 ^ (n - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ d /
              ((3 ^ n : ℕ) : ℝ) ^ d) / 2 +
            σ * (√(1 / ((3 ^ n : ℕ) : ℝ)) +
              √(1 - ((((3 ^ (n - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ d / ((3 ^ n : ℕ) : ℝ) ^ d) +
              √(1 / ((3 ^ k : ℕ) : ℝ)))) *
            ∑ y ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
              (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                (cubeDatum hd hP m hU u (y + unit j) - cubeDatum hd hP m hU u y) ^ 2 else 0)) +
          2 * (σ / √((3 ^ n : ℕ) : ℝ) *
            ∑ y ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
              (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                (cubeDatum hd hP m hU u (y + unit j) - cubeDatum hd hP m hU u y) ^ 2 else 0))) /
          (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d +
        σ * ((2 * d * ((r + 1 + 3 ^ n : ℕ) : ℝ) /
            ((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ)) ^ (1 - 2 / s) *
          ((d : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s *
              (((3 ^ n : ℕ) : ℝ) / r) ^ s)) *
              ∑ y ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
                (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                  |cubeDatum hd hP m hU u (y + unit j) - cubeDatum hd hP m hU u y| ^ s
                  else 0)) /
              (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d) ^ (2 / s)) := by
  set Q := (⟨m, 0⟩ : TriadicCube d).toIntegerCube with hQ
  set w := cubeDatum hd hP m hU u with hw
  set a : Fin d → ℝ := fun _ => σ with ha
  set N := 3 ^ n with hNdef
  set K := 3 ^ k with hKdef
  set M := 3 ^ (n - k) - 1 with hMdef
  set A := (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1) with hA
  have hN : 0 < N := by positivity
  have hK : 0 < K := by positivity
  have hL : 0 < Q.size := by change 0 < 3 ^ m; positivity
  have hMK : (M + 1) * K ≤ N := by
    change (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
  have htests := fun x (hx : x ∈ A) =>
    exists_cube_mu_test (r := r) hd hP hkn hkm hU hk hu a hx
  choose! μ hμ using htests
  set μT : Vertex d → Vertex d → ℝ := fun x i =>
    cubeMu ω (gridTile k (triadicGridCorner k x) i) (fun j => a j * cubeSlope N w x j)
  set δ : Vertex d → ℝ := fun x =>
    (∑ i ∈ (cornerCube 0 M).vertices, ((K : ℕ) : ℝ) ^ d *
        |(∑ j, (a j * cubeSlope N w x j) ^ 2 / a j) / 2 + μT x i|) / ((N : ℕ) : ℝ) ^ d +
      |1 - ((cornerCube (0 : Vertex d) M).vertices.card : ℝ) * ((K : ℕ) : ℝ) ^ d /
        ((N : ℕ) : ℝ) ^ d| * |(∑ j, (a j * cubeSlope N w x j) ^ 2 / a j) / 2| +
      |∑ j, a j * cubeSlope N w x j * (cubeEdgeSlope N w x j -
        (∑ i ∈ (cornerCube 0 M).vertices, ((K : ℕ) : ℝ) ^ d *
          cubeEdgeSlope K w (triadicGridCorner k x + ((K : ℕ) : ℤ) • i) j) / ((N : ℕ) : ℝ) ^ d)|
    with hδ
  have key := innerEdgeEnergy_dirichletSolution_div_le_of_mu_test (d := d) (by omega) a
    (fun _ => hσ) (Λ := σ) (fun _ => le_rfl) Q hL hN hr w hs μ δ (cubeEnergy ω ⟨m, 0⟩ u)
    (cubeEnergy_nonneg _ u) (fun x hx => (hμ x hx).1) (fun x hx => (hμ x hx).2)
  have hsum := sum_subcube_errors_le a hσ.le (fun _ => hσ) (fun _ => le_rfl) hK hMK w A Q.vertices
    (fun x hx y hy => ⟨(mem_of_mem_cornerCube_of_mem_trim Q hx hy ⟨0, hd⟩).1,
      fun j => (mem_of_mem_cornerCube_of_mem_trim Q hx hy j).2⟩)
    (triadicGridCorner k) (fun x _ t => by
      have := triadicGridCorner_spec k x t
      rw [hKdef]
      push_cast
      exact ⟨this.1, this.2.1⟩) μT hε0 (fun x hx i hi => by
      obtain ⟨-, hint⟩ := gridTile_vertices_subset (r := r) hkn hx hi
      have hTU : (gridTile k (triadicGridCorner k x) i).vertices ⊆
          (⟨m, 0⟩ : TriadicCube d).vertices := fun y hy =>
        (TriadicCube.mem_toIntegerCube_vertices _ y).1 (Finset.filter_subset _ _ (hint y hy))
      exact hconv _ rfl hTU _)
  rw [sum_cubeEnergy_eq_innerEdgeEnergy] at key
  refine key.trans ?_
  have hsum' : 2 * ∑ x ∈ A, δ x ≤ 2 * ((ε * σ ^ 2 + σ * (1 - (((M * K : ℕ) : ℝ)) ^ d /
      ((N : ℕ) : ℝ) ^ d) / 2 + σ * (√(1 / ((N : ℕ) : ℝ)) +
        √(1 - (((M * K : ℕ) : ℝ)) ^ d / ((N : ℕ) : ℝ) ^ d) + √(1 / ((K : ℕ) : ℝ)))) *
      ∑ y ∈ Q.vertices, ∑ j : Fin d,
        (if y + unit j ∈ Q.vertices then (w (y + unit j) - w y) ^ 2 else 0)) := by
    have := hsum
    linarith
  gcongr

end Rigidity.Dirichlet
