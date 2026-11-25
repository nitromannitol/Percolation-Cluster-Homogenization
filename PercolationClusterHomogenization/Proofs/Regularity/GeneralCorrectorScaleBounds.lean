import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorSupBound
import PercolationClusterHomogenization.Proofs.Regularity.GeneralScaleMaxima
import PercolationClusterHomogenization.Proofs.Cluster.PartitionCoarseData
import PercolationClusterHomogenization.Proofs.Cluster.CoarseReach

/-!
# The bounds on the corrector at one triadic scale of `ℤᵈ`

The deterministic inputs of the uniform bound of the corrector at the scale `3^m` (Armstrong and
Dario, arXiv:1609.09431v2, Remark after (1.19)), in every dimension:

* `partitionCoarseData_card_bounds`: the regions, the pair regions and the partition cubes of the
  coarse-graining data of a resolved cube have at most `7^d Z^d` vertices when the partition cubes
  have sides at most `Z`;
* `sum_sq_le_card_mul_componentBallL2_sq`: a sum of squares on a cluster ball from its normalized
  norm;
* `abs_corrector_sub_le_of_lipschitz`: the increments of the corrector along the open edges at a
  vertex from the Lipschitz estimate at that vertex;
* `componentBallL2_le_of_density`: the normalized norm on the ball `B_{3^m}(z)` around a vertex of
  the box `{|z_i| ≤ 14 · 3^m}` against the one on `B_{15 d 3^m}`, from the density of the cluster;
* `componentSlopeAsymptotics_of_scale_bound`: the slope asymptotics from a uniform bound
  `c (3^m)^{1-η}` of the corrector on the boxes `{|x_i| ≤ 3^m}`.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

/-- The regions, the pair regions and the partition cubes of the coarse-graining data of a resolved
cube have at most `7^d Z^d` vertices when the partition cubes of its vertices have sides at most
`Z`. -/
theorem partitionCoarseData_card_bounds (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) {Z : ℝ}
    (hZ : ∀ y ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω y).scale ≤ Z) :
    (∀ x ∈ (partitionCoarseData hd hP U hU).cluster,
      (((partitionCoarseData hd hP U hU).region x ∩
        (partitionCoarseData hd hP U hU).cluster).card : ℝ) ≤ 7 ^ d * Z ^ d) ∧
    (∀ x ∈ (partitionCoarseData hd hP U hU).domain, ∀ y ∈ (partitionCoarseData hd hP U hU).domain,
      (((partitionCoarseData hd hP U hU).pairRegion x y ∩
        (partitionCoarseData hd hP U hU).cluster).card : ℝ) ≤ 7 ^ d * Z ^ d) ∧
    (∀ x ∈ (partitionCoarseData hd hP U hU).domain,
      (((partitionCoarseData hd hP U hU).part x).toIntegerCube.vertices.card : ℝ) ≤
        7 ^ d * Z ^ d) := by
  have h7 : (1 : ℝ) ≤ 7 ^ d := one_le_pow₀ (by norm_num)
  have h72 : (2 : ℝ) ≤ 7 ^ d := by
    calc (2 : ℝ) ≤ 7 ^ 1 := by norm_num
      _ ≤ 7 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hpow : ∀ y ∈ U.vertices, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤ Z ^ d :=
    fun y hy => pow_le_pow_left₀ (by positivity) (hZ y hy) d
  have hcube : ∀ y ∈ U.vertices,
      (((partitionCube ω y).toIntegerCube.vertices.card : ℕ) : ℝ) ≤ Z ^ d := by
    intro y hy
    rw [card_toIntegerCube_vertices_pow]
    exact hpow y hy
  have hZ0 : ∀ y ∈ U.vertices, 0 ≤ Z ^ d := fun y hy =>
    (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d).trans (hpow y hy)
  have hdom : ∀ x ∈ (partitionCoarseData hd hP U hU).domain, x ∈ U.vertices := fun x hx =>
    (TriadicCube.mem_toIntegerCube_vertices U x).1 hx
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx => ?_⟩
  · have hxU : x ∈ U.vertices :=
      (TriadicCube.mem_toIntegerCube_vertices U x).1 (Finset.mem_filter.1 hx).1
    have hsub : (partitionCoarseData hd hP U hU).region x ∩
        (partitionCoarseData hd hP U hU).cluster ⊆ ((partitionCube ω x).thicken 3).vertices :=
      Finset.inter_subset_left.trans (partitionRegion_subset_thicken hP U x)
    have hc := Finset.card_le_card hsub
    rw [TriadicCube.card_thicken] at hc
    calc (((partitionCoarseData hd hP U hU).region x ∩
          (partitionCoarseData hd hP U hU).cluster).card : ℝ)
        ≤ (((2 * 3 + 1) ^ d * 3 ^ ((partitionCube ω x).scale * d) : ℕ) : ℝ) := by
          exact_mod_cast hc
      _ = 7 ^ d * ((3 : ℝ) ^ (partitionCube ω x).scale) ^ d := by
          push_cast
          ring
      _ ≤ 7 ^ d * Z ^ d := mul_le_mul_of_nonneg_left (hpow x hxU) (by positivity)
  · have hxU := hdom x hx
    have hyU := hdom y hy
    have hsub : (partitionCoarseData hd hP U hU).pairRegion x y ∩
        (partitionCoarseData hd hP U hU).cluster ⊆
          (partitionCube ω x).toIntegerCube.vertices ∪
            (partitionCube ω y).toIntegerCube.vertices := by
      intro z hz
      have hz' := (Finset.mem_filter.1 (Finset.mem_inter.1 hz).1).2
      rcases hz' with h | h
      · exact Finset.mem_union_left _ ((TriadicCube.mem_toIntegerCube_vertices _ z).2 h)
      · exact Finset.mem_union_right _ ((TriadicCube.mem_toIntegerCube_vertices _ z).2 h)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    calc (((partitionCoarseData hd hP U hU).pairRegion x y ∩
          (partitionCoarseData hd hP U hU).cluster).card : ℝ)
        ≤ (((partitionCube ω x).toIntegerCube.vertices.card : ℕ) : ℝ) +
            (((partitionCube ω y).toIntegerCube.vertices.card : ℕ) : ℝ) := by
          exact_mod_cast hc
      _ ≤ Z ^ d + Z ^ d := add_le_add (hcube x hxU) (hcube y hyU)
      _ ≤ 7 ^ d * Z ^ d := by nlinarith [hZ0 x hxU]
  · have hxU := hdom x hx
    calc (((partitionCoarseData hd hP U hU).part x).toIntegerCube.vertices.card : ℝ)
        ≤ Z ^ d := hcube x hxU
      _ ≤ 7 ^ d * Z ^ d := le_mul_of_one_le_left (hZ0 x hxU) h7

/-- A sum of squares on a cluster ball from its normalized norm. -/
theorem sum_sq_le_card_mul_componentBallL2_sq (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (f : C → ℝ) :
    ∑ x ∈ componentEuclideanBall C z r, f x ^ 2 ≤
      ((componentEuclideanBall C z r).card : ℝ) * componentBallL2 C z r f ^ 2 := by
  unfold componentBallL2
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C z r).card with h0 | h0
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · have hn : (0 : ℝ) < (componentEuclideanBall C z r).card := by exact_mod_cast h0
    rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hn.le),
      mul_div_cancel₀ _ hn.ne']

/-- **The increments of the corrector along the open edges at `z`** from the Lipschitz estimate at
`z` at the scale `ρ ∈ [𝒳_z, R/2]` and a bound `B` of the normalized norm of the corrector on
`B_R(z)`. -/
theorem abs_corrector_sub_le_of_lipschitz (C : OpenComponent ω) (q : Fin d → ℝ) (u : C → ℝ)
    (hu : ∀ x, componentLaplacian C u x = 0) (z : C) {Yz R ρ C₀ B : ℝ}
    (hLip : ∀ R : ℝ, 2 * Yz ≤ R → ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C z.val R,
        (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C z.val R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Yz ≤ r → r ≤ R / 2 →
        componentBallL2 C z.val r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C z.val R v)
    (hR : 2 * Yz ≤ R) (hρY : Yz ≤ ρ) (hρ1 : 1 < ρ) (hρR : ρ ≤ R / 2) (hC₀ : 0 ≤ C₀)
    (hB : componentBallL2 C z.val R (componentCorrector C q u) ≤ B)
    {y : C} (hzy : (componentGraph C).Adj z y) :
    |componentCorrector C q u y - componentCorrector C q u z| ≤
      2 * (2 * ρ + 3) ^ d * C₀ * (ρ / R) * (B + (∑ i, |q i|) * R) + ∑ i, |q i| := by
  have hR0 : 0 < R := by linarith
  have happ : ∀ a : ℝ, ∃ c : ℝ, componentBallL2 C z.val ρ ((fun y => u y - a) - fun _ => c) ≤
      C₀ * (ρ / R) * componentBallL2 C z.val R (fun y => u y - a) := by
    intro a
    obtain ⟨c, hc⟩ := hLip R hR (fun y => u y - a) fun x _ _ => by
      rw [componentLaplacian_sub_const]; exact hu x
    exact ⟨c, hc ρ hρY hρR⟩
  have hadj : (openGraph ω).Adj z.val y.val := hzy
  have hdist := dist_le_one_of_lattice_adj_general (openGraph_le ω hadj)
  have hz : z ∈ componentEuclideanBall C z.val ρ := by
    rw [mem_componentEuclideanBall, dist_self]; linarith
  have hy : y ∈ componentEuclideanBall C z.val ρ := by
    rw [mem_componentEuclideanBall]; linarith
  refine (abs_corrector_sub_le C q u z hR0 hC₀ (by linarith) happ hz hy hdist).trans ?_
  gcongr

/-- **The normalized norm on a ball around a vertex of a box** from the one on a large ball around
the origin and the density of the cluster: for `|z_i| ≤ 14 · 3^m`,
`‖f‖_{L̲²(B_{3^m}(z))} ≤ ((33 d)^d 3^{d(d+1)} / κ)^{1/2} ‖f‖_{L̲²(B_{15 d 3^m})}`. -/
theorem componentBallL2_le_of_density [NeZero d] (C : OpenComponent ω) {ℓ κ : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 ((d : ℝ) * (14 * 3 ^ (d + 1) + 1) + 1) ℓ κ) {m : ℕ}
    (hm : d + 1 ≤ m) (hℓ : ℓ ≤ 3 ^ (m - (d + 1))) {z : Vertex d}
    (hz : ∀ i, |((z i : ℤ) : ℝ)| ≤ 14 * 3 ^ m) (f : C → ℝ) :
    componentBallL2 C z (3 ^ m) f ≤
      Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) *
        componentBallL2 C 0 (15 * d * 3 ^ m) f := by
  set k := m - (d + 1) with hk
  have hmk : m = k + (d + 1) := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have h3k : (3 : ℝ) ^ m = 3 ^ (d + 1) * 3 ^ k := by rw [hmk, pow_add, mul_comm]
  have hT : (0 : ℝ) < 3 ^ m := by positivity
  have hzk : ∀ i, |((z i : ℤ) : ℝ)| ≤ (14 * 3 ^ (d + 1)) * 3 ^ k := by
    intro i
    have := hz i
    rw [h3k] at this
    linarith
  have hlow := card_componentEuclideanBall_ge C hcube hℓ hzk (by linarith)
  have h2d : (2 * d : ℝ) ≤ 3 ^ (d + 1) := by exact_mod_cast two_mul_le_three_pow_succ d
  have hsub1 : componentEuclideanBall C z (2 * d * 3 ^ k) ⊆ componentEuclideanBall C z (3 ^ m) := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx ⊢
    have : (2 * d : ℝ) * 3 ^ k ≤ 3 ^ (d + 1) * 3 ^ k :=
      mul_le_mul_of_nonneg_right h2d (by positivity)
    linarith
  have hlow' : κ * 3 ^ (d * k) ≤ (componentEuclideanBall C z (3 ^ m)).card :=
    hlow.trans (by exact_mod_cast Finset.card_le_card hsub1)
  have hpos : 0 < (componentEuclideanBall C z (3 ^ m)).card := by
    have : (0 : ℝ) < κ * 3 ^ (d * k) := by positivity
    exact_mod_cast this.trans_le hlow'
  -- the ball around `z` lies in the ball around the origin
  have hz0 : dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding (0 : Vertex d)) ≤
      14 * d * 3 ^ m := by
    have h := dist_latticeEuclideanEmbedding_le (y := z) (w := latticeEuclideanEmbedding 0)
      (a := 14 * 3 ^ m) (by positivity) fun i => by
        have e : latticeEuclideanEmbedding (0 : Vertex d) i = 0 := by
          simp [latticeEuclideanEmbedding]
        rw [e, sub_zero]; exact hz i
    calc _ ≤ Real.sqrt d * (14 * 3 ^ m) := h
      _ ≤ d * (14 * 3 ^ m) := mul_le_mul_of_nonneg_right sqrt_le_self_of_neZero (by positivity)
      _ = 14 * d * 3 ^ m := by ring
  have hsub : componentEuclideanBall C z (3 ^ m) ⊆ componentEuclideanBall C 0 (15 * d * 3 ^ m) := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx ⊢
    have := dist_triangle (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding z)
      (latticeEuclideanEmbedding (0 : Vertex d))
    have : (3 : ℝ) ^ m ≤ d * 3 ^ m := le_mul_of_one_le_left hT.le hd1
    linarith
  refine (componentBallL2_le_of_subset C hsub hpos f).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (componentBallL2_nonneg _ _ _ _))
  -- the ratio of the cardinalities
  have hn : (0 : ℝ) < (componentEuclideanBall C z (3 ^ m)).card := by exact_mod_cast hpos
  rw [div_le_div_iff₀ hn hκ]
  have hbig := card_componentEuclideanBall_le C (0 : Vertex d)
    (by positivity : (0 : ℝ) ≤ 15 * d * 3 ^ m)
  have h33 : 2 * (15 * d * (3 : ℝ) ^ m) + 3 ≤ 33 * d * 3 ^ m := by
    have h1 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hbig' : ((componentEuclideanBall C 0 (15 * d * 3 ^ m)).card : ℝ) ≤ (33 * d * 3 ^ m) ^ d :=
    hbig.trans (pow_le_pow_left₀ (by positivity) h33 d)
  have e : ((33 * d : ℝ) * 3 ^ m) ^ d = (33 * d) ^ d * 3 ^ (d * (d + 1)) * 3 ^ (d * k) := by
    rw [mul_pow, ← pow_mul, show m * d = d * (d + 1) + d * k by rw [hmk]; ring, pow_add,
      mul_assoc]
  calc ((componentEuclideanBall C 0 (15 * d * 3 ^ m)).card : ℝ) * κ
      ≤ (33 * d * 3 ^ m) ^ d * κ := mul_le_mul_of_nonneg_right hbig' hκ.le
    _ = (33 * d) ^ d * 3 ^ (d * (d + 1)) * (κ * 3 ^ (d * k)) := by rw [e]; ring
    _ ≤ (33 * d) ^ d * 3 ^ (d * (d + 1)) * (componentEuclideanBall C z (3 ^ m)).card :=
        mul_le_mul_of_nonneg_left hlow' (by positivity)

/-- **The slope asymptotics from a uniform bound at the triadic scales**: if the corrector is at
most `c (3^m)^{1-η}` on the vertices of `C` in the box `{|x_i| ≤ 3^m}` for all large `m`, then
`u` has the slope `q` at infinity. -/
theorem componentSlopeAsymptotics_of_scale_bound (C : OpenComponent ω) (q : Fin d → ℝ)
    (u : C → ℝ) {c η : ℝ} (hη : 0 < η) (hc : 0 ≤ c) {m₀ : ℕ}
    (h : ∀ m : ℕ, m₀ ≤ m → ∀ x : C, (∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ m) →
      |u x - componentSlope C q x| ≤ c * ((3 : ℝ) ^ m) ^ (1 - η)) :
    componentSlopeAsymptotics C q u := by
  intro ε hε
  set R₀ : ℝ := max ((3 : ℝ) ^ m₀) (max 1 ((3 * c / ε) ^ (1 / η))) with hR₀
  refine ⟨R₀, lt_of_lt_of_le one_pos ((le_max_left 1 _).trans (le_max_right _ _)),
    fun R hR x hx => ?_⟩
  have hR1 : 1 ≤ R := ((le_max_left 1 _).trans (le_max_right _ _)).trans hR
  have hR0 : 0 < R := by linarith
  have hRm₀ : (3 : ℝ) ^ m₀ ≤ R := (le_max_left _ _).trans hR
  have hRc : (3 * c / ε) ^ (1 / η) ≤ R := ((le_max_right 1 _).trans (le_max_right _ _)).trans hR
  -- the triadic scale of `R`
  have hex : ∃ m : ℕ, R ≤ 3 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 3)
    exact ⟨m, hm.le⟩
  set m := Nat.find hex with hmdef
  have hRm : R ≤ 3 ^ m := Nat.find_spec hex
  have hm₀ : m₀ ≤ m := by
    by_contra hlt
    push Not at hlt
    have h1 : (3 : ℝ) ^ m < 3 ^ m₀ := pow_lt_pow_right₀ (by norm_num) hlt
    linarith
  have h3m : (3 : ℝ) ^ m ≤ 3 * R := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero]; linarith
    · have hmin := Nat.find_min hex (show m - 1 < m by omega)
      push Not at hmin
      have e : (3 : ℝ) ^ m = 3 * 3 ^ (m - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel h0]
      rw [e]; linarith
  -- the bound at `x`
  have hxb : ∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ m := by
    intro i
    rw [mem_componentEuclideanBall] at hx
    have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex d) i
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h1
    linarith
  refine (h m hm₀ x hxb).trans ?_
  have hE0 : (0 : ℝ) < 3 ^ m := by positivity
  have hsplit : ((3 : ℝ) ^ m) ^ (1 - η) = 3 ^ m / ((3 : ℝ) ^ m) ^ η := by
    rw [Real.rpow_sub hE0, Real.rpow_one]
  rw [hsplit]
  have hRη : R ^ η ≤ ((3 : ℝ) ^ m) ^ η := Real.rpow_le_rpow hR0.le hRm hη.le
  have hRη0 : 0 < R ^ η := Real.rpow_pos_of_pos hR0 η
  have hcR : 3 * c ≤ ε * R ^ η := by
    have h1 : (3 * c / ε) ≤ R ^ η := by
      have h2 := Real.rpow_le_rpow (by positivity) hRc hη.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one] at h2
    rw [div_le_iff₀ hε] at h1
    linarith
  calc c * (3 ^ m / ((3 : ℝ) ^ m) ^ η) ≤ c * (3 * R / R ^ η) :=
        mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) h3m hRη0 hRη) hc
    _ = 3 * c * R / R ^ η := by ring
    _ ≤ ε * R ^ η * R / R ^ η :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcR hR0.le) hRη0.le
    _ = ε * R := by field_simp

end Rigidity.Proofs.Regularity.GeneralDim
