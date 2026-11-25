import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorScaleBounds
import PercolationClusterHomogenization.Proofs.Regularity.GeneralGradNormBound
import PercolationClusterHomogenization.Proofs.Regularity.GeneralClusterInclusions

/-!
# The uniform bound of the corrector at one triadic scale of `ℤᵈ`

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19), in every dimension: at the scale
`E = 3^m`, on the partition event, if the partition cubes of `□_{m+3}` have sides at most `3 Y₀`
and scales at most `m`, the minimal scales of the Lipschitz estimate at the vertices of `□_{m+3}`
are at most `3 Y₀`, `10 Y₀ ≤ E`, the cluster has the density `κ` in the triadic cubes around the
origin and `‖χ‖_{L̲²(𝒞_∞ ∩ B_{15 d E})} ≤ b`, then for every vertex `x` of the infinite cluster with
`|x_i| ≤ E` (`abs_corrector_le_at_scale`)
`|χ(x)| ≤ A (2 d L) + (2 A M₂ (t + 1)^{-d} + 2 (d t A (2 d L))²)^{1/2}`,
with `A = 7^d (3 Y₀)^d`, `M₂ = (33 d E)^d b²` and `L` the bound of the increments of `χ` along the
open edges from the Lipschitz estimate at their endpoints (`abs_corrector_sub_le_of_lipschitz`).
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

theorem abs_le_of_mem_cube_zero {j : ℕ} {z : Vertex d}
    (hz : z ∈ (⟨j, 0⟩ : TriadicCube d).vertices) (i : Fin d) :
    2 * |((z i : ℤ) : ℝ)| < 3 ^ j := by
  have h := (mem_triadicCube_zero_iff'.1 hz) i
  have h' : ((2 * |z i| : ℤ) : ℝ) < (((3 : ℤ) ^ j : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- **The uniform bound of the corrector at the scale `3^m`.** -/
theorem abs_corrector_le_at_scale [NeZero d] (hP : PartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) (q : Fin d → ℝ) (u : C → ℝ)
    (hu : ∀ x, componentLaplacian C u x = 0) {m : ℕ} (hm : d + 1 ≤ m) {Y₀ C₀ κ ℓ b : ℝ}
    {Yz : Vertex d → ℝ} (hY₀ : 1 ≤ Y₀) (hY₀E : 10 * Y₀ ≤ 3 ^ m) (hC₀ : 0 ≤ C₀) (hκ : 0 < κ)
    (hsc : ∀ y ∈ (⟨m + 3, 0⟩ : TriadicCube d).vertices,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ 3 * Y₀)
    (hscm : ∀ y ∈ triadicCubeFinset d (m + 3) 0, (partitionCube ω y).scale ≤ m)
    (hLip : ∀ z : C, ∀ R : ℝ, 2 * Yz z.val ≤ R → ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C z.val R,
        (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C z.val R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Yz z.val ≤ r → r ≤ R / 2 →
        componentBallL2 C z.val r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C z.val R v)
    (hYz : ∀ z ∈ (⟨m + 3, 0⟩ : TriadicCube d).vertices, Yz z ≤ 3 * Y₀)
    (hcube : ClusterCubeDensity C 0 ((d : ℝ) * (14 * 3 ^ (d + 1) + 1) + 1) ℓ κ)
    (hℓ : ℓ ≤ 3 ^ (m - (d + 1)))
    (hb : componentBallL2 C 0 (15 * d * 3 ^ m) (componentCorrector C q u) ≤ b)
    (t : ℕ) (ht : (t : ℝ) ≤ 3 ^ m) (x : C) (hx : ∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ m) :
    |componentCorrector C q u x| ≤
      7 ^ d * (3 * Y₀) ^ d * (2 * d * (2 * (2 * (3 * Y₀ + 2) + 3) ^ d * C₀ *
        ((3 * Y₀ + 2) / 3 ^ m) * (Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * b +
          (∑ i, |q i|) * 3 ^ m) + ∑ i, |q i|)) +
      Real.sqrt (2 * (7 ^ d * (3 * Y₀) ^ d) * ((33 * d * 3 ^ m) ^ d * b ^ 2) /
          ((t : ℝ) + 1) ^ d +
        2 * (d * t * (7 ^ d * (3 * Y₀) ^ d * (2 * d * (2 * (2 * (3 * Y₀ + 2) + 3) ^ d * C₀ *
          ((3 * Y₀ + 2) / 3 ^ m) * (Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * b +
            (∑ i, |q i|) * 3 ^ m) + ∑ i, |q i|)))) ^ 2) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  set U : TriadicCube d := ⟨m + 3, 0⟩ with hUdef
  set E : ℝ := 3 ^ m with hE
  have hE0 : 0 < E := by positivity
  have hE1 : 1 ≤ E := one_le_pow₀ (by norm_num)
  have h27 : (3 : ℝ) ^ (m + 3) = 27 * E := by rw [hE]; ring
  have hU : PartitionResolved ω U := fun z hz => by
    have := hscm z (mem_cubeFinset_iff_vertices.2 hz)
    show (partitionCube ω z).scale ≤ m + 3
    omega
  set P := partitionCoarseData hd0 hP U hU with hPdef
  obtain ⟨hreg, hpair, hpart⟩ := partitionCoarseData_card_bounds hd0 hP hU hsc
  -- the vertex `x` lies in `C_*(U)`
  have hxZ : ∀ k, 2 * |x.val k| < 17 * 3 ^ m := by
    intro k
    have h1 := hx k
    have h2 : ((|x.val k| : ℤ) : ℝ) ≤ (((3 : ℤ) ^ m : ℤ) : ℝ) := by push_cast; exact h1
    have h3 : |x.val k| ≤ 3 ^ m := by exact_mod_cast h2
    have h4 : (0 : ℤ) < 3 ^ m := by positivity
    linarith
  have hxcl : x.val ∈ crossingClusterVertices ω U :=
    mem_crossingClusterVertices_inner_cube hd0 hP C hinf hscm x.2 hxZ
  have hxU : x.val ∈ U.vertices :=
    (TriadicCube.mem_toIntegerCube_vertices U x.val).1 (Finset.mem_filter.1 hxcl).1
  have hCsub : ∀ y ∈ crossingClusterVertices ω U, y ∈ C.supp := fun y hy =>
    mem_supp_of_mem_crossingClusterVertices hd0 hP hU C hinf hxU x.2 hy
  -- the vertices of `U`
  have hUbox : ∀ y ∈ U.vertices, ∀ i, |((y i : ℤ) : ℝ)| ≤ 14 * E := by
    intro y hy i
    have := abs_le_of_mem_cube_zero hy i
    rw [h27] at this
    linarith
  have hUdist : ∀ y ∈ U.vertices,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) ≤
        14 * d * E := by
    intro y hy
    have h := dist_latticeEuclideanEmbedding_le (y := y) (w := latticeEuclideanEmbedding 0)
      (a := 14 * E) (by positivity) fun i => by
        have e : latticeEuclideanEmbedding (0 : Vertex d) i = 0 := by
          simp [latticeEuclideanEmbedding]
        rw [e, sub_zero]; exact hUbox y hy i
    calc _ ≤ Real.sqrt d * (14 * E) := h
      _ ≤ d * (14 * E) := mul_le_mul_of_nonneg_right sqrt_le_self_of_neZero (by positivity)
      _ = 14 * d * E := by ring
  -- the function on the lattice
  set χ := componentCorrector C q u with hχ
  set w : Vertex d → ℝ := Rigidity.Section3.extend C χ with hwdef
  have hw : ∀ y (hy : y ∈ C.supp), w y = χ ⟨y, hy⟩ := by
    intro y hy
    simp [hwdef, Rigidity.Section3.extend, hy]
  have hb0 : 0 ≤ b := (componentBallL2_nonneg _ _ _ _).trans hb
  -- the increments along the open edges
  set ρ : ℝ := 3 * Y₀ + 2 with hρ
  set B : ℝ := Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * b with hB
  set L : ℝ := 2 * (2 * ρ + 3) ^ d * C₀ * (ρ / E) * (B + (∑ i, |q i|) * E) + ∑ i, |q i| with hL
  have hL0 : 0 ≤ L := by positivity
  have hLb : ∀ z ∈ P.cluster, ∀ y ∈ P.cluster, (openGraph ω).Adj z y → |w z - w y| ≤ L := by
    intro z hz y hy hzy
    have hzC := hCsub z hz
    have hyC := hCsub y hy
    have hzU : z ∈ U.vertices :=
      (TriadicCube.mem_toIntegerCube_vertices U z).1 (Finset.mem_filter.1 hz).1
    rw [hw z hzC, hw y hyC, abs_sub_comm]
    have hBz : componentBallL2 C z (3 ^ m) χ ≤ B := by
      refine (componentBallL2_le_of_density C hκ hcube hm hℓ (hUbox z hzU) χ).trans ?_
      exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    have hYzz := hYz z hzU
    exact abs_corrector_sub_le_of_lipschitz C q u hu ⟨z, hzC⟩ (hLip ⟨z, hzC⟩)
      (by linarith) (by linarith) (by linarith) (by linarith) hC₀ hBz hzy
  -- the sum of the squares on `C_*(U)`
  have hM₂ : ∑ z ∈ P.cluster, w z ^ 2 ≤ (33 * d * E) ^ d * b ^ 2 := by
    set S := componentEuclideanBall C 0 (15 * d * E) with hS
    have hsub : P.cluster ⊆ S.map (Function.Embedding.subtype _) := by
      intro y hy
      have hyC := hCsub y hy
      have hyU : y ∈ U.vertices :=
        (TriadicCube.mem_toIntegerCube_vertices U y).1 (Finset.mem_filter.1 hy).1
      refine Finset.mem_map.2 ⟨⟨y, hyC⟩, ?_, rfl⟩
      rw [hS, mem_componentEuclideanBall]
      have h1 := hUdist y hyU
      have h2 : 14 * d * E < 15 * d * E := by nlinarith
      exact lt_of_le_of_lt h1 h2
    have h1 : ∑ z ∈ P.cluster, w z ^ 2 ≤ ∑ z ∈ S.map (Function.Embedding.subtype _), w z ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    rw [Finset.sum_map] at h1
    have h2 : ∑ z ∈ S, w ((Function.Embedding.subtype _) z) ^ 2 = ∑ z ∈ S, χ z ^ 2 :=
      Finset.sum_congr rfl fun z _ => by
        rw [Function.Embedding.coe_subtype, hw z.val z.2]
    rw [h2] at h1
    refine h1.trans ((sum_sq_le_card_mul_componentBallL2_sq C 0 _ χ).trans ?_)
    have hcard := card_componentEuclideanBall_le C (0 : Vertex d)
      (by positivity : (0 : ℝ) ≤ 15 * d * E)
    have h33 : 2 * (15 * d * E) + 3 ≤ 33 * d * E := by nlinarith
    have hcard' : (S.card : ℝ) ≤ (33 * d * E) ^ d :=
      hcard.trans (pow_le_pow_left₀ (by positivity) h33 d)
    have hsq : componentBallL2 C 0 (15 * d * E) χ ^ 2 ≤ b ^ 2 :=
      pow_le_pow_left₀ (componentBallL2_nonneg _ _ _ _) hb 2
    exact mul_le_mul hcard' hsq (sq_nonneg _) (by positivity)
  -- the box `x + [0, t]ᵈ` lies in `U`
  have hbox : ∀ y : Vertex d, (∀ i, x.val i ≤ y i ∧ y i ≤ x.val i + t) → y ∈ P.domain := by
    intro y hy
    refine (TriadicCube.mem_toIntegerCube_vertices U y).2 (mem_triadicCube_zero_iff'.2 fun i => ?_)
    have h1 := hx i
    have h2 : ((|x.val i| : ℤ) : ℝ) ≤ (((3 : ℤ) ^ m : ℤ) : ℝ) := by push_cast; exact h1
    have h3 : |x.val i| ≤ 3 ^ m := by exact_mod_cast h2
    have ht' : (t : ℤ) ≤ 3 ^ m := by
      have : ((t : ℤ) : ℝ) ≤ (((3 : ℤ) ^ m : ℤ) : ℝ) := by push_cast; exact ht
      exact_mod_cast this
    have h4 : (0 : ℤ) < 3 ^ m := by positivity
    have e : (3 : ℤ) ^ (m + 3) = 27 * 3 ^ m := by ring
    obtain ⟨hy1, hy2⟩ := hy i
    rw [e]
    rcases abs_cases (y i) with ⟨hh, _⟩ | ⟨hh, _⟩ <;>
      rcases abs_cases (x.val i) with ⟨hh', _⟩ | ⟨hh', _⟩ <;> rw [hh] <;> rw [hh'] at h3 <;>
        omega
  have hA0 : (0 : ℝ) ≤ 7 ^ d * (3 * Y₀) ^ d := by positivity
  have hmain := abs_le_of_coarseData P w hL0 hA0 hLb hreg hpair hpart hM₂ hxcl t hbox
  rw [hw x.val x.2] at hmain
  exact hmain

end Rigidity.Proofs.Regularity.GeneralDim
