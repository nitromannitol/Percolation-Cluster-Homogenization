import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralClusterTiles
import PercolationClusterHomogenization.Proofs.Cluster.SobolevPartition

/-!
# The Poincaré inequality on the cluster of a cube of `ℤᵈ` for functions vanishing on its boundary

Let `U` be a triadic cube and `U'` its parent, with all partition cubes of the vertices of `U'` of
scale at most `k ≤ scale(U)`, and let `f` vanish off the vertices of `C_*(U)` whose lattice
neighbours lie in `U`. Then `f` vanishes on `C_*(U') \ C_*(U)`, which contains the anchors of the
partition cubes of the vertices of `U' \ U`, hence at least `(3^d − 1) 3^{d(scale(U) − k)}` vertices
(`card_le_mul_card_sdiff_crossingClusterVertices`). The mean-zero Sobolev inequality on `C_*(U')`
(Armstrong and Dario, Proposition 3.4, `s = 2`, `t = 2d/(d + 2)`,
`exists_partition_sum_rpow_le_of_sum_eq_zero`) applied to `f − f̄`, the bound `3^{ρ} ≤ 3^k` of the
reach scales and the power-mean inequality `(Σ G^t)^{2/t} ≤ |C|^{2/d} Σ G²` give
`Σ_{C_*(U)} f² ≤ (1 + 3^d/(3^d − 1) 3^{dk}) K (3^k)^{2d} (3^{scale(U)+1})² Σ_{open edges of C_*(U)} (∇f)²`
(`exists_cube_sum_sq_le_of_eq_zero`). This is Proposition 3.4 of the source with `s = 2` for
functions vanishing on the boundary, as used in the proofs of Lemma 6.3 and Proposition 6.1, with
the size of the partition cubes entering through their maximum, in every dimension; the planar
form is `exists_planar_sum_sq_le_of_eq_zero`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

theorem gradNormIn_fun_sub_const (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (c : ℝ) (x : Vertex d) :
    gradNormIn G S (fun y => f y - c) x = gradNormIn G S f x := by
  unfold gradNormIn
  congr 2
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- **The power-mean inequality** for the exponents `t ≤ 2`:
`(Σ G^t)^{2/t} ≤ |s|^{2/t − 1} Σ G²`. -/
theorem rpow_sum_rpow_le_card_rpow_mul_sum_sq {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {G : ι → ℝ} (hG : ∀ i ∈ s, 0 ≤ G i) {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) :
    (∑ i ∈ s, G i ^ t) ^ (2 / t) ≤ (s.card : ℝ) ^ (2 / t - 1) * ∑ i ∈ s, G i ^ 2 := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hp : 1 ≤ 2 / t := by rw [le_div_iff₀ ht0]; linarith
  have hw : ∑ _i ∈ s, (1 / (s.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h1 : (∑ i ∈ s, 1 / (s.card : ℝ) * G i ^ t) ^ (2 / t) ≤
      ∑ i ∈ s, 1 / (s.card : ℝ) * (G i ^ t) ^ (2 / t) :=
    Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / (s.card : ℝ)) (fun i => G i ^ t)
      (fun _ _ => by positivity) hw (fun i hi => Real.rpow_nonneg (hG i hi) t) hp
  have e : ∀ i ∈ s, (G i ^ t) ^ (2 / t) = G i ^ 2 := by
    intro i hi
    rw [← Real.rpow_mul (hG i hi), show t * (2 / t) = 2 by field_simp]
    exact Real.rpow_two (G i)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_congr rfl e] at h1
  have hS : 0 ≤ ∑ i ∈ s, G i ^ t := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hG i hi) t
  rw [Real.mul_rpow (by positivity) hS, Real.div_rpow zero_le_one hn.le, Real.one_rpow] at h1
  have hN : (0 : ℝ) < (s.card : ℝ) ^ (2 / t) := Real.rpow_pos_of_pos hn _
  rw [Real.rpow_sub_one hn.ne']
  rw [one_div_mul_eq_div, one_div_mul_eq_div, div_le_div_iff₀ hN hn] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  linarith

/-- The reach scales of the coarse-graining data of a resolved cube are at most the largest scale
of the partition cubes of its vertices. -/
theorem reachScale_partitionCoarseData_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ k) (z : Vertex d) :
    (partitionCoarseData hd hP U hU).reachScale z ≤ k := by
  refine Finset.sup_le fun x hx => ?_
  have hxC : x ∈ crossingClusterVertices ω U := (Finset.mem_filter.1 hx).1
  exact hk x (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 hxC))

/-- An open neighbour inside `U` of a vertex of `C_*(U)` is in `C_*(U)`. -/
theorem mem_crossingClusterVertices_of_adj {U : TriadicCube d} {x y : Vertex d}
    (hx : x ∈ crossingClusterVertices ω U) (hyU : y ∈ U.vertices) (hadj : (openGraph ω).Adj x y) :
    y ∈ crossingClusterVertices ω U :=
  mem_crossingClusterVertices.2
    (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 hx) hyU hadj)

/-- The cluster vertices of `U' \ U` number at least `|U' \ U| / 3^{dk}`. -/
theorem card_le_mul_card_sdiff_crossingClusterVertices (hd : 0 < d) (hP : PartitionEvent ω)
    {U U' : TriadicCube d} (hU' : PartitionResolved ω U') {k : ℕ} (hkU : k ≤ U.scale)
    (hk : ∀ x ∈ U'.vertices, (partitionCube ω x).scale ≤ k) :
    (U'.toIntegerCube.vertices \ U.toIntegerCube.vertices).card ≤
      3 ^ (d * k) * (crossingClusterVertices ω U' \ crossingClusterVertices ω U).card := by
  set A := U'.toIntegerCube.vertices \ U.toIntegerCube.vertices
  set f : Vertex d → Vertex d := partitionAnchor ω
  have himage : A.image f ⊆ crossingClusterVertices ω U' \ crossingClusterVertices ω U := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨hxU', hxU⟩ := Finset.mem_sdiff.1 hx
    rw [U'.mem_toIntegerCube_vertices] at hxU'
    rw [U.mem_toIntegerCube_vertices] at hxU
    refine Finset.mem_sdiff.2 ⟨mem_crossingClusterVertices.2
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hU' hxU'), fun h => ?_⟩
    have hfU := U.crossingCluster_subset ω (mem_crossingClusterVertices.1 h)
    have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le (partitionAnchor_mem hP x) hfU
      ((hk x hxU').trans hkU)
    exact hxU (hsub (mem_partitionCube hP x))
  have hfib : ∀ a ∈ A.image f, (A.filter fun x => f x = a).card ≤ 3 ^ (d * k) := by
    intro a ha
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 ha
    have hx₀U' : x₀ ∈ U'.vertices :=
      (U'.mem_toIntegerCube_vertices x₀).1 (Finset.mem_sdiff.1 hx₀).1
    have hsub : A.filter (fun x => f x = f x₀) ⊆
        (partitionCube ω x₀).toIntegerCube.vertices := by
      intro x hx
      obtain ⟨-, hfx⟩ := Finset.mem_filter.1 hx
      have ha1 := partitionAnchor_mem hP x
      have ha0 := partitionAnchor_mem hP x₀
      change partitionAnchor ω x = partitionAnchor ω x₀ at hfx
      rw [hfx] at ha1
      have e1 := partitionCube_eq_of_mem hP ha1
      have e0 := partitionCube_eq_of_mem hP ha0
      rw [e0] at e1
      rw [TriadicCube.mem_toIntegerCube_vertices, e1]
      exact mem_partitionCube hP x
    refine (Finset.card_le_card hsub).trans ?_
    rw [IntegerCube.card_vertices_eq]
    change (3 ^ (partitionCube ω x₀).scale) ^ d ≤ 3 ^ (d * k)
    rw [← pow_mul, mul_comm (partitionCube ω x₀).scale d]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left d (hk x₀ hx₀U'))
  calc A.card = ∑ a ∈ A.image f, (A.filter fun x => f x = a).card :=
        Finset.card_eq_sum_card_image f A
    _ ≤ ∑ _a ∈ A.image f, 3 ^ (d * k) := Finset.sum_le_sum hfib
    _ = 3 ^ (d * k) * (A.image f).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 ^ (d * k) * (crossingClusterVertices ω U' \ crossingClusterVertices ω U).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himage)

/-- The lattice neighbours of a vertex whose lattice neighbours lie in the cube lie in the cube. -/
theorem TriadicCube.add_sub_unit_mem_of_isLatticeInterior {U : TriadicCube d} {x : Vertex d}
    (hx : U.IsLatticeInterior x) (k : Fin d) :
    x + unit k ∈ U.vertices ∧ x - unit k ∈ U.vertices :=
  ⟨hx _ (Graph.Zd.adj_iff.mpr ⟨k, Or.inl rfl⟩), hx _ (Graph.Zd.adj_iff.mpr ⟨k, Or.inr rfl⟩)⟩

/-- The edge energy of `f` on the open edges of `C_*(U')` reduces to `C_*(U)` when `f` vanishes
off the vertices of `C_*(U)` whose lattice neighbours lie in `U`. -/
theorem sum_edges_le_of_support (hd : 0 < d) (hP : PartitionEvent ω) {U U' : TriadicCube d}
    (hUU' : U.vertices ⊆ U'.vertices) (hU : PartitionResolved ω U) (hscale : U.scale ≤ U'.scale)
    (f : Vertex d → ℝ)
    (hf : ∀ x, ¬(x ∈ crossingClusterVertices ω U ∧ U.IsLatticeInterior x) → f x = 0) :
    ∑ z ∈ crossingClusterVertices ω U', ∑ k : Fin d,
        (if z + unit k ∈ crossingClusterVertices ω U' ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0) ≤
      ∑ z ∈ crossingClusterVertices ω U, ∑ k : Fin d,
        (if z + unit k ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0) := by
  set C := crossingClusterVertices ω U'
  set C₀ := crossingClusterVertices ω U
  have hC₀C : C₀ ⊆ C := crossingClusterVertices_subset_of_resolved hd hP hU hUU' hscale
  have hterm : ∀ z ∈ C, ∀ k : Fin d,
      (if z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k) then (f (z + unit k) - f z) ^ 2
        else 0) ≤
      if z ∈ C₀ then (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
        (f (z + unit k) - f z) ^ 2 else 0) else 0 := by
    intro z _ k
    by_cases h1 : z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k)
    · rw [if_pos h1]
      by_cases hz0 : z ∈ C₀ ∧ z + unit k ∈ C₀
      · rw [if_pos hz0.1, if_pos ⟨hz0.2, h1.2⟩]
      · have hfz : f z = 0 := by
          refine hf z fun ⟨hzC, hzI⟩ => hz0 ⟨hzC, ?_⟩
          exact mem_crossingClusterVertices_of_adj hzC
            (TriadicCube.add_sub_unit_mem_of_isLatticeInterior hzI k).1 h1.2
        have hfz' : f (z + unit k) = 0 := by
          refine hf _ fun ⟨hzC, hzI⟩ => hz0 ⟨?_, hzC⟩
          have hzU : z ∈ U.vertices := by
            have := (TriadicCube.add_sub_unit_mem_of_isLatticeInterior hzI k).2
            rwa [add_sub_cancel_right] at this
          exact mem_crossingClusterVertices_of_adj hzC hzU h1.2.symm
        rw [hfz, hfz', sub_zero, sq, mul_zero]
        split_ifs <;> exact le_rfl
    · rw [if_neg h1]
      split_ifs <;> positivity
  calc ∑ z ∈ C, ∑ k : Fin d,
        (if z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0)
      ≤ ∑ z ∈ C, ∑ k : Fin d, (if z ∈ C₀ then
          (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
            (f (z + unit k) - f z) ^ 2 else 0) else 0) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun k _ => hterm z hz k
    _ = ∑ z ∈ C₀, ∑ k : Fin d,
          (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
            (f (z + unit k) - f z) ^ 2 else 0) := by
        have e : ∀ z, ∑ k : Fin d, (if z ∈ C₀ then
            (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
              (f (z + unit k) - f z) ^ 2 else 0) else 0) =
            if z ∈ C₀ then ∑ k : Fin d,
              (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
                (f (z + unit k) - f z) ^ 2 else 0) else 0 := fun z => by
          split_ifs <;> simp
        simp only [e]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hC₀C]

/-- The sum of the squared gradients on `C_*(U')` is at most the edge energy on `C_*(U)` when `f`
vanishes off the vertices of `C_*(U)` whose lattice neighbours lie in `U`. -/
theorem sum_gradNormIn_sq_le_of_support (hd : 0 < d) (hP : PartitionEvent ω)
    {U U' : TriadicCube d} (hUU' : U.vertices ⊆ U'.vertices) (hU : PartitionResolved ω U)
    (hscale : U.scale ≤ U'.scale) (f : Vertex d → ℝ)
    (hf : ∀ x, ¬(x ∈ crossingClusterVertices ω U ∧ U.IsLatticeInterior x) → f x = 0) :
    ∑ z ∈ crossingClusterVertices ω U',
        gradNormIn (openGraph ω) (crossingClusterVertices ω U') f z ^ 2 ≤
      ∑ z ∈ crossingClusterVertices ω U, ∑ k : Fin d,
        (if z + unit k ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0) := by
  set C := crossingClusterVertices ω U'
  have h1 : ∑ z ∈ C, gradNormIn (openGraph ω) C f z ^ 2 = (1 / 2) * ∑ z ∈ C, ∑ y ∈ C,
      (if (openGraph ω).Adj z y then (f z - f y) ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [gradNormIn]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by
      split_ifs <;> positivity))]
  rw [h1, sum_sum_openAdj_eq_two_mul_sum_unit C (fun z y => (f z - f y) ^ 2) (fun z y => by ring)]
  have e : ∀ z j, (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then
      (f z - f (z + unit j)) ^ 2 else 0) =
      (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then
        (f (z + unit j) - f z) ^ 2 else 0) := fun z j => by split_ifs <;> ring
  simp only [e]
  have := sum_edges_le_of_support hd hP hUU' hU hscale f hf
  linarith

/-- The factor of the Sobolev inequality after the bound of the reach scales and the power-mean
inequality: `(Σ_z (3^{ρ(z)})^{t d} G_z^t)^{2/t} ≤ (3^k)^{2d} |C|^{2/d} Σ G²`, `t = 2d/(d + 2)`. -/
theorem rpow_sum_weight_le (hd : 2 ≤ d) {C : Finset (Vertex d)} (hC : C.Nonempty)
    {ρ : Vertex d → ℕ} {k : ℕ} (hρ : ∀ z, ρ z ≤ k) {G : Vertex d → ℝ} (hG : ∀ z, 0 ≤ G z) :
    (∑ z ∈ C, ((3 : ℝ) ^ ρ z) ^ (2 * (d : ℝ) / (2 + d) * d) * G z ^ (2 * (d : ℝ) / (2 + d))) ^
        (2 / (2 * (d : ℝ) / (2 + d))) ≤
      ((3 : ℝ) ^ k) ^ (2 * d) * ((C.card : ℝ) ^ (2 / (d : ℝ)) * ∑ z ∈ C, G z ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set t : ℝ := 2 * (d : ℝ) / (2 + d) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht2 : t ≤ 2 := by rw [ht, div_le_iff₀ (by positivity)]; linarith
  have ht1 : 2 / t - 1 = 2 / d := by rw [ht]; field_simp; ring
  have hW : ∀ z, ((3 : ℝ) ^ ρ z) ^ (t * d) ≤ ((3 : ℝ) ^ k) ^ (t * d) := fun z =>
    Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (hρ z)) (by positivity)
  have hS : 0 ≤ ∑ z ∈ C, G z ^ t := Finset.sum_nonneg fun z _ => Real.rpow_nonneg (hG z) t
  have hstep : ∑ z ∈ C, ((3 : ℝ) ^ ρ z) ^ (t * d) * G z ^ t ≤
      ((3 : ℝ) ^ k) ^ (t * d) * ∑ z ∈ C, G z ^ t := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_right (hW z) (Real.rpow_nonneg (hG z) t)
  have hX : 0 ≤ ∑ z ∈ C, ((3 : ℝ) ^ ρ z) ^ (t * d) * G z ^ t :=
    Finset.sum_nonneg fun z _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hG z) t)
  refine (Real.rpow_le_rpow hX hstep (by positivity)).trans ?_
  rw [Real.mul_rpow (by positivity) hS]
  have htne : t ≠ 0 := ht0.ne'
  have e1 : (((3 : ℝ) ^ k) ^ (t * d)) ^ (2 / t) = ((3 : ℝ) ^ k) ^ (2 * d) := by
    rw [← Real.rpow_mul (by positivity)]
    have e : t * (d : ℝ) * (2 / t) = ((2 * d : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e, Real.rpow_natCast]
  rw [e1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h2 := rpow_sum_rpow_le_card_rpow_mul_sum_sq hC (fun z _ => hG z) ht0 ht2
  rwa [ht1] at h2

/-- **Proposition 3.4 with `s = 2` for functions vanishing on the boundary**, in every dimension
`d ≥ 2`. There is `K` such that, if all partition cubes of the vertices of the parent of a triadic
cube `U` have scale at most `k ≤ scale(U)` and `f` vanishes off the vertices of `C_*(U)` whose
lattice neighbours lie in `U`, then
`Σ_{C_*(U)} f² ≤ (1 + 3^d/(3^d − 1) 3^{dk}) K (3^k)^{2d} (3^{scale(U)+1})² Σ_{open edges of C_*(U)} (∇f)²`.
The source states Proposition 3.4 with the moments of the sizes of the partition cubes; here they
enter through their maximum `3^k`. -/
theorem exists_cube_sum_sq_le_of_eq_zero (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d), PartitionEvent ω → ∀ (U : TriadicCube d)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (partitionCube ω x).scale ≤ k) →
      ∀ f : Vertex d → ℝ,
      (∀ x, ¬(x ∈ crossingClusterVertices ω U ∧ U.IsLatticeInterior x) → f x = 0) →
      ∑ x ∈ crossingClusterVertices ω U, f x ^ 2 ≤
        (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) * K * ((3 : ℝ) ^ k) ^ (2 * d) *
          ((3 : ℝ) ^ (U.scale + 1)) ^ 2 *
          ∑ z ∈ crossingClusterVertices ω U, ∑ j : Fin d,
            (if z + unit j ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hs : (d : ℝ) / (d - 1) ≤ 2 := by
    rw [div_le_iff₀ hdm]
    linarith
  obtain ⟨K, hK, hsob⟩ := exists_partition_sum_rpow_le_of_sum_eq_zero hd (s := 2)
    (t := 2 * d / (2 + d)) hs rfl
  refine ⟨K, hK, fun ω hP U k hkm hk f hf => ?_⟩
  set m := U.scale
  set U' : TriadicCube d := U.parent
  have hUU' : U.vertices ⊆ U'.vertices := U.vertices_subset_parent
  have hsc : U.scale ≤ U'.scale := by change U.scale ≤ U.scale + 1; omega
  have hU' : PartitionResolved ω U' := fun z hz => (hk z hz).trans (by change k ≤ U.scale + 1; omega)
  have hU : PartitionResolved ω U := fun z hz => (hk z (hUU' hz)).trans hkm
  set C := crossingClusterVertices ω U'
  set C₀ := crossingClusterVertices ω U
  have hC₀C : C₀ ⊆ C := crossingClusterVertices_subset_of_resolved hd0 hP hU hUU' hsc
  set E₀ := ∑ z ∈ C₀, ∑ j : Fin d,
    (if z + unit j ∈ C₀ ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2 else 0)
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity
  have hf0 : ∀ x, x ∉ C₀ → f x = 0 := fun x hx => hf x fun h => hx h.1
  -- the counting of `C \ C₀`
  have hcount := card_le_mul_card_sdiff_crossingClusterVertices hd0 hP (U := U) (U' := U')
    hU' hkm hk
  have hcardU : U.toIntegerCube.vertices.card = 3 ^ (d * m) := by
    rw [IntegerCube.card_vertices_eq]
    change (3 ^ U.scale) ^ d = 3 ^ (d * U.scale)
    rw [← pow_mul, mul_comm]
  have hcardU' : U'.toIntegerCube.vertices.card = 3 ^ d * 3 ^ (d * m) := by
    rw [IntegerCube.card_vertices_eq]
    change (3 ^ (U.scale + 1)) ^ d = 3 ^ d * 3 ^ (d * U.scale)
    rw [← pow_mul, ← pow_add]
    ring_nf
  have hUU'f : U.toIntegerCube.vertices ⊆ U'.toIntegerCube.vertices := fun x hx => by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx ⊢
    exact hUU' hx
  have hsd := Finset.card_sdiff_add_card_eq_card hUU'f
  rw [hcardU, hcardU'] at hsd
  set D := C \ C₀
  have h3d : (1 : ℝ) < 3 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hb : (0 : ℝ) < 3 ^ (d * m) := by positivity
  have hD : ((3 : ℝ) ^ d - 1) * 3 ^ (d * m) ≤ 3 ^ (d * k) * D.card := by
    have h1 : ((U'.toIntegerCube.vertices \ U.toIntegerCube.vertices).card : ℝ) ≤
        3 ^ (d * k) * D.card := by exact_mod_cast hcount
    have h2 : ((U'.toIntegerCube.vertices \ U.toIntegerCube.vertices).card : ℝ) +
        3 ^ (d * m) = 3 ^ d * 3 ^ (d * m) := by exact_mod_cast hsd
    nlinarith
  have hDpos : (0 : ℝ) < D.card := by
    have : (0 : ℝ) < ((3 : ℝ) ^ d - 1) * 3 ^ (d * m) := mul_pos (by linarith) hb
    have h9 : (0 : ℝ) < 3 ^ (d * k) := by positivity
    nlinarith
  have hCcard : (C.card : ℝ) ≤ 3 ^ d * 3 ^ (d * m) := by
    have : C.card ≤ U'.toIntegerCube.vertices.card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [hcardU'] at this
    exact_mod_cast this
  have hCne : C.Nonempty := by
    have : 0 < D.card := by exact_mod_cast hDpos
    obtain ⟨x, hx⟩ := Finset.card_pos.1 this
    exact ⟨x, (Finset.mem_sdiff.1 hx).1⟩
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hCne.card_pos
  -- the mean of `f` on `C`
  set fbar := (∑ x ∈ C, f x) / C.card
  set g : Vertex d → ℝ := fun y => f y - fbar
  have hg0 : ∑ x ∈ C, g x = 0 := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hCpos.ne']
    ring
  have hsobg := hsob ω hP U' hU' g hg0
  have hL : ∑ x ∈ C, |g x| ^ (2 : ℝ) = ∑ x ∈ C, g x ^ 2 :=
    Finset.sum_congr rfl fun x _ => by rw [Real.rpow_two, sq_abs]
  rw [hL] at hsobg
  simp only [g, gradNormIn_fun_sub_const] at hsobg
  have hW := rpow_sum_weight_le hd hCne
    (reachScale_partitionCoarseData_le hd0 hP hU' (fun x hx => hk x hx))
    (fun z => gradNormIn_nonneg (openGraph ω) C f z)
  have hG := sum_gradNormIn_sq_le_of_support hd0 hP hUU' hU hsc f hf
  have hdne : (d : ℝ) ≠ 0 := by positivity
  have hCpow : (C.card : ℝ) ^ (2 / (d : ℝ)) ≤ ((3 : ℝ) ^ (U.scale + 1)) ^ 2 := by
    have hC' : (C.card : ℝ) ≤ ((3 : ℝ) ^ (U.scale + 1)) ^ d := by
      refine hCcard.trans (le_of_eq ?_)
      rw [← pow_mul, ← pow_add]
      ring_nf
      rfl
    calc (C.card : ℝ) ^ (2 / (d : ℝ)) ≤ (((3 : ℝ) ^ (U.scale + 1)) ^ d) ^ (2 / (d : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hC' (by positivity)
      _ = ((3 : ℝ) ^ (U.scale + 1)) ^ 2 := by
          rw [← Real.rpow_natCast ((3 : ℝ) ^ (U.scale + 1)) d, ← Real.rpow_mul (by positivity),
            show (d : ℝ) * (2 / d) = 2 by field_simp [hdne], Real.rpow_two]
  have hg2 : ∑ x ∈ C, g x ^ 2 ≤
      K * (((3 : ℝ) ^ k) ^ (2 * d) * (((3 : ℝ) ^ (U.scale + 1)) ^ 2 * E₀)) := by
    refine hsobg.trans (mul_le_mul_of_nonneg_left (hW.trans ?_) hK)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hCpow hG (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  -- the mean
  have hmean : (C.card : ℝ) * fbar ^ 2 ≤ C.card / D.card * ∑ x ∈ C, g x ^ 2 := by
    have hDsum : ∑ x ∈ D, g x ^ 2 = D.card * fbar ^ 2 := by
      rw [Finset.sum_congr rfl fun x hx => by
        rw [show g x = -fbar by simp only [g, hf0 x (Finset.mem_sdiff.1 hx).2, zero_sub]]]
      rw [Finset.sum_const, nsmul_eq_mul, neg_sq]
    have hDle : ∑ x ∈ D, g x ^ 2 ≤ ∑ x ∈ C, g x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
    rw [hDsum] at hDle
    rw [div_mul_eq_mul_div, le_div_iff₀ hDpos]
    nlinarith
  have hsplit : ∑ x ∈ C, f x ^ 2 = ∑ x ∈ C, g x ^ 2 + C.card * fbar ^ 2 := by
    have : ∀ x, f x ^ 2 = g x ^ 2 + 2 * fbar * g x + fbar ^ 2 := fun x => by simp only [g]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hg0, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hratio : (C.card : ℝ) / D.card ≤ 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k) := by
    rw [div_le_iff₀ hDpos]
    have h3 : (0 : ℝ) < 3 ^ d - 1 := by linarith
    have : (3 : ℝ) ^ d * 3 ^ (d * m) ≤ 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k) * D.card := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h3]
      nlinarith
    linarith
  have hgg : 0 ≤ ∑ x ∈ C, g x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ x ∈ C₀, f x ^ 2 ≤ ∑ x ∈ C, f x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hC₀C fun _ _ _ => sq_nonneg _
    _ ≤ (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) * ∑ x ∈ C, g x ^ 2 := by
        rw [hsplit]
        nlinarith
    _ ≤ (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) *
          (K * (((3 : ℝ) ^ k) ^ (2 * d) * (((3 : ℝ) ^ (U.scale + 1)) ^ 2 * E₀))) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
    _ = (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) * K * ((3 : ℝ) ^ k) ^ (2 * d) *
          ((3 : ℝ) ^ (U.scale + 1)) ^ 2 * E₀ := by ring

end Rigidity.Dirichlet
