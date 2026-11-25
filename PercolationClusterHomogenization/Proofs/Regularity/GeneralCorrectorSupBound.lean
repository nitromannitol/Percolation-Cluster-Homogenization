import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorFromApproximation
import PercolationClusterHomogenization.Proofs.Cluster.CoarseInequalities
import PercolationClusterHomogenization.Proofs.Regularity.DiscreteTaylor

/-!
# The uniform bound of a function on a cluster from its `L²` norm and its open increments

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19), in every dimension: the
interpolation inequality between `L²` and `C^{0,1}` on a box of `ℤᵈ`, applied to the coarsening
`[w]_𝒫` of `w` on coarse-graining data, and the comparison of `w` with `[w]_𝒫` along the local open
paths (the pointwise forms of Lemmas 3.2 and 3.3) bound `w` at a vertex of the cluster
(`abs_le_of_coarseData`): if the open increments of `w` on the cluster are at most `L`, the regions
of the coarse-graining data and the partition cubes have at most `A` vertices, `∑ w² ≤ M₂` on the
cluster and the box `x + [0, t]ᵈ` lies in the domain, then
`|w(x)| ≤ 2 d A L + (2 A M₂ (t + 1)^{-d} + 2 (d t · 2 d A L)²)^{1/2}`.

* `vertexVariation_le_of_forall_le`: the sum of the open increments at a vertex is at most `2 d L`;
* `abs_sub_le_of_fwd_box`: increments of a function along monotone lattice paths in a box;
* `sum_coarsen_sq_le`: the sum of `[w]_𝒫²` over a part of the domain counts each anchor at most
  `A` times.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

/-- The sum of the open increments at a vertex is at most `2 d L` when each is at most `L`. -/
theorem vertexVariation_le_of_forall_le (S : Finset (Vertex d)) (w : Vertex d → ℝ) (x : Vertex d)
    {L : ℝ} (hL : 0 ≤ L) (h : ∀ y ∈ S, (openGraph ω).Adj x y → |w x - w y| ≤ L) :
    vertexVariation ω S w x ≤ 2 * d * L := by
  set T := S.filter ((openGraph ω).Adj x)
  have hV : vertexVariation ω S w x = ∑ y ∈ T, |w x - w y| := by
    rw [vertexVariation, Finset.sum_filter]
  have hT : (T.card : ℝ) ≤ 2 * d := by
    have h1 : T ⊆ (openGraph ω).neighborFinset x := fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
    exact_mod_cast ((Finset.card_le_card h1).trans
      ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans (openGraph_degree_le ω x)))
  rw [hV]
  calc ∑ y ∈ T, |w x - w y| ≤ ∑ _y ∈ T, L := Finset.sum_le_sum fun y hy =>
        h y (Finset.mem_filter.1 hy).1 (Finset.mem_filter.1 hy).2
    _ = T.card * L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * L := mul_le_mul_of_nonneg_right hT hL

/-- **Increments along monotone lattice paths in a box.** If the forward increments of `g` at the
points of the box `x + [0, t]ᵈ` that stay in the box are at most `L`, then
`|g(x + v) - g(x)| ≤ (∑ i, v i) L` for `v ∈ [0, t]ᵈ`. -/
theorem abs_sub_le_of_fwd_box (g : Vertex d → ℝ) (x : Vertex d) (t : ℕ) {L : ℝ}
    (h : ∀ y : Vertex d, (∀ i, x i ≤ y i ∧ y i ≤ x i + t) → ∀ i, y i < x i + t →
      |g (y + unit i) - g y| ≤ L)
    (v : Fin d → ℕ) (hv : ∀ i, v i ≤ t) :
    |g (x + fun i => (v i : ℤ)) - g x| ≤ (∑ i, (v i : ℝ)) * L := by
  have key : ∀ s : Finset (Fin d),
      |g (x + fun i => if i ∈ s then (v i : ℤ) else 0) - g x| ≤ (∑ i ∈ s, (v i : ℝ)) * L := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have e : (x + fun i => if i ∈ (∅ : Finset (Fin d)) then (v i : ℤ) else 0) = x := by
          funext i
          simp
        rw [e, sub_self, abs_zero, Finset.sum_empty, zero_mul]
    | insert a s ha ih =>
        set q : Vertex d := x + fun i => if i ∈ s then (v i : ℤ) else 0 with hq
        have e : (x + fun i => if i ∈ insert a s then (v i : ℤ) else 0) =
            q + (v a : ℤ) • unit a := by
          funext i
          simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mem_insert, unit,
            Pi.single_apply]
          by_cases hia : i = a
          · subst hia; simp [ha]
          · simp [hia]
        have hseg := abs_sub_le_of_fwd_le g q a (v a) (M := L) fun t' ht' => by
          simp only [fwd]
          refine h _ (fun i => ?_) a ?_
          · simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
            by_cases hia : i = a
            · subst hia
              have := hv i
              simp only [ha, if_false, if_true, add_zero, mul_one]
              constructor <;> omega
            · have := hv i
              simp only [hia, if_false, mul_zero, add_zero]
              split_ifs <;> constructor <;> omega
          · simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply, ha,
              if_false, if_true, add_zero, mul_one]
            have := hv a
            omega
        rw [e, Finset.sum_insert ha, add_mul]
        calc |g (q + (v a : ℤ) • unit a) - g x|
            ≤ |g (q + (v a : ℤ) • unit a) - g q| + |g q - g x| := abs_sub_le _ _ _
          _ ≤ (v a : ℝ) * L + (∑ i ∈ s, (v i : ℝ)) * L := add_le_add hseg ih
  have e : (x + fun i => (v i : ℤ)) = x + fun i => if i ∈ (Finset.univ : Finset (Fin d)) then
      (v i : ℤ) else 0 := by simp
  rw [e]
  exact key Finset.univ

/-- The coarsened function varies by at most `A (2 d L)` across a lattice edge of the domain. -/
theorem abs_coarsen_sub_le (P : CoarseData d ω) (w : Vertex d → ℝ) {L A : ℝ} (hL0 : 0 ≤ L)
    (hA0 : 0 ≤ A)
    (hL : ∀ z ∈ P.cluster, ∀ y ∈ P.cluster, (openGraph ω).Adj z y → |w z - w y| ≤ L)
    (hpair : ∀ x ∈ P.domain, ∀ y ∈ P.domain, ((P.pairRegion x y ∩ P.cluster).card : ℝ) ≤ A)
    {x y : Vertex d} (hx : x ∈ P.domain) (hy : y ∈ P.domain)
    (hxy : (nearestNeighborGraph d).Adj x y) :
    |P.coarsen w x - P.coarsen w y| ≤ A * (2 * d * L) := by
  by_cases hne : P.part x = P.part y
  · rw [P.coarsen_congr w hne, sub_self, abs_zero]; positivity
  · have h := P.abs_coarsen_sub_rpow_le w (s := 1) le_rfl hx hy hxy hne
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul] at h
    refine h.trans ?_
    calc ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z
        ≤ ∑ _z ∈ P.pairRegion x y ∩ P.cluster, 2 * d * L := Finset.sum_le_sum fun z hz =>
          vertexVariation_le_of_forall_le _ w z hL0 fun y' hy' hzy =>
            hL z (Finset.mem_inter.1 hz).2 y' hy' hzy
      _ = ((P.pairRegion x y ∩ P.cluster).card : ℝ) * (2 * d * L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A * (2 * d * L) := mul_le_mul_of_nonneg_right (hpair x hx y hy) (by positivity)

/-- The sum of the squares of the coarsening over a part of the domain counts each anchor at most
`A` times. -/
theorem sum_coarsen_sq_le (P : CoarseData d ω) (w : Vertex d → ℝ) {A : ℝ} (hA0 : 0 ≤ A)
    (hpart : ∀ x ∈ P.domain, ((P.part x).toIntegerCube.vertices.card : ℝ) ≤ A)
    (Q : Finset (Vertex d)) (hQ : Q ⊆ P.domain) :
    ∑ y ∈ Q, P.coarsen w y ^ 2 ≤ A * ∑ z ∈ P.cluster, w z ^ 2 := by
  have e1 : ∑ y ∈ Q, P.coarsen w y ^ 2 =
      ∑ z ∈ P.cluster, ∑ y ∈ Q with P.anchor y = z, w z ^ 2 :=
    (Finset.sum_fiberwise_of_maps_to' (fun y hy => P.anchor_mem y (hQ hy))
      (fun z => w z ^ 2)).symm
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg (w z))
  by_cases hne : (Q.filter (fun y => P.anchor y = z)).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hy₀Q := (Finset.mem_filter.1 hy₀).1
    have hy₀z := (Finset.mem_filter.1 hy₀).2
    have hsub : Q.filter (fun y => P.anchor y = z) ⊆ (P.part y₀).toIntegerCube.vertices := by
      intro y hy
      have hyQ := (Finset.mem_filter.1 hy).1
      have hyz := (Finset.mem_filter.1 hy).2
      have h2 : P.part (P.anchor y) = P.part y :=
        P.part_eq_of_mem y (hQ hyQ) _ (P.anchor_mem_part y (hQ hyQ))
      have h2' : P.part (P.anchor y₀) = P.part y₀ :=
        P.part_eq_of_mem y₀ (hQ hy₀Q) _ (P.anchor_mem_part y₀ (hQ hy₀Q))
      have hpe : P.part y = P.part y₀ := by rw [← h2, ← h2', hyz, hy₀z]
      rw [TriadicCube.mem_toIntegerCube_vertices, ← hpe]
      exact P.mem_part y (hQ hyQ)
    exact (Nat.cast_le.2 (Finset.card_le_card hsub)).trans (hpart y₀ (hQ hy₀Q))
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simpa using hA0

/-- **The uniform bound at a vertex of the cluster** from the open increments, the sizes of the
regions and of the partition cubes, and the sum of the squares on the cluster, by the comparison
with the coarsening and the interpolation inequality on the box `x + [0, t]ᵈ`. -/
theorem abs_le_of_coarseData (P : CoarseData d ω) (w : Vertex d → ℝ) {L A M₂ : ℝ} (hL0 : 0 ≤ L)
    (hA0 : 0 ≤ A)
    (hL : ∀ z ∈ P.cluster, ∀ y ∈ P.cluster, (openGraph ω).Adj z y → |w z - w y| ≤ L)
    (hreg : ∀ x ∈ P.cluster, ((P.region x ∩ P.cluster).card : ℝ) ≤ A)
    (hpair : ∀ x ∈ P.domain, ∀ y ∈ P.domain, ((P.pairRegion x y ∩ P.cluster).card : ℝ) ≤ A)
    (hpart : ∀ x ∈ P.domain, ((P.part x).toIntegerCube.vertices.card : ℝ) ≤ A)
    (hM₂ : ∑ z ∈ P.cluster, w z ^ 2 ≤ M₂) {x : Vertex d} (hx : x ∈ P.cluster) (t : ℕ)
    (hbox : ∀ y : Vertex d, (∀ i, x i ≤ y i ∧ y i ≤ x i + t) → y ∈ P.domain) :
    |w x| ≤ A * (2 * d * L) +
      Real.sqrt (2 * A * M₂ / ((t : ℝ) + 1) ^ d + 2 * (d * t * (A * (2 * d * L))) ^ 2) := by
  set g := P.coarsen w with hg
  set L' := A * (2 * d * L) with hL'
  have hL'0 : 0 ≤ L' := by positivity
  -- the coarsening error at `x`
  have herr : |w x - g x| ≤ L' := by
    have h := P.abs_sub_coarsen_rpow_le w (s := 1) le_rfl hx
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul] at h
    refine h.trans ?_
    calc ∑ z ∈ P.region x ∩ P.cluster, vertexVariation ω P.cluster w z
        ≤ ∑ _z ∈ P.region x ∩ P.cluster, 2 * d * L := Finset.sum_le_sum fun z hz =>
          vertexVariation_le_of_forall_le _ w z hL0 fun y hy hzy =>
            hL z (Finset.mem_inter.1 hz).2 y hy hzy
      _ = ((P.region x ∩ P.cluster).card : ℝ) * (2 * d * L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L' := mul_le_mul_of_nonneg_right (hreg x hx) (by positivity)
  -- the box `x + [0, t]ᵈ`
  set Q : Finset (Vertex d) := Fintype.piFinset fun i => Finset.Icc (x i) (x i + t) with hQ
  have hmemQ : ∀ y, y ∈ Q ↔ ∀ i, x i ≤ y i ∧ y i ≤ x i + t := by
    intro y
    simp only [hQ, Fintype.mem_piFinset, Finset.mem_Icc]
  have hQdom : Q ⊆ P.domain := fun y hy => hbox y ((hmemQ y).1 hy)
  have hcardQ : (Q.card : ℝ) = ((t : ℝ) + 1) ^ d := by
    have hI : ∀ i, (Finset.Icc (x i) (x i + t)).card = t + 1 := by
      intro i
      rw [Int.card_Icc]
      omega
    rw [hQ, Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hI i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  -- the increments along the box
  have hpath : ∀ y ∈ Q, |g y - g x| ≤ d * t * L' := by
    intro y hy
    have hy' := (hmemQ y).1 hy
    set v : Fin d → ℕ := fun i => (y i - x i).toNat with hv
    have hvt : ∀ i, v i ≤ t := fun i => by
      have := hy' i
      simp only [hv]
      omega
    have hyv : y = x + fun i => (v i : ℤ) := by
      funext i
      have := hy' i
      simp only [hv, Pi.add_apply]
      omega
    have h := abs_sub_le_of_fwd_box g x t (L := L') (fun z hz i hzi => by
      have hz1 : z ∈ P.domain := hbox z hz
      have hz2 : z + unit i ∈ P.domain := hbox _ fun j => by
        have := hz j
        simp only [Pi.add_apply, unit, Pi.single_apply]
        split_ifs with hji
        · subst hji
          constructor <;> omega
        · simpa using this
      have hadj : (nearestNeighborGraph d).Adj (z + unit i) z := ⟨i, Or.inr rfl⟩
      exact abs_coarsen_sub_le P w hL0 hA0 hL hpair hz2 hz1 hadj) v hvt
    rw [← hyv] at h
    refine h.trans ?_
    have hsum : (∑ i, (v i : ℝ)) ≤ d * t := by
      calc (∑ i, (v i : ℝ)) ≤ ∑ _i : Fin d, (t : ℝ) :=
            Finset.sum_le_sum fun i _ => by exact_mod_cast hvt i
        _ = d * t := by simp
    exact mul_le_mul_of_nonneg_right hsum hL'0
  -- the averaging over the box
  have hsq : ∀ y ∈ Q, g x ^ 2 ≤ 2 * g y ^ 2 + 2 * (d * t * L') ^ 2 := by
    intro y hy
    have h1 := hpath y hy
    have h2 : (g x - g y) ^ 2 ≤ (d * t * L') ^ 2 := by
      rw [← sq_abs, abs_sub_comm]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (g x - 2 * g y)]
  have hS : ∑ y ∈ Q, g y ^ 2 ≤ A * M₂ :=
    (sum_coarsen_sq_le P w hA0 hpart Q hQdom).trans (mul_le_mul_of_nonneg_left hM₂ hA0)
  have hsumQ : (Q.card : ℝ) * g x ^ 2 ≤ 2 * (A * M₂) + Q.card * (2 * (d * t * L') ^ 2) := by
    have h1 : ∑ _y ∈ Q, g x ^ 2 ≤ ∑ y ∈ Q, (2 * g y ^ 2 + 2 * (d * t * L') ^ 2) :=
      Finset.sum_le_sum hsq
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  have hQpos : (0 : ℝ) < Q.card := by rw [hcardQ]; positivity
  have hgx : g x ^ 2 ≤ 2 * A * M₂ / ((t : ℝ) + 1) ^ d + 2 * (d * t * L') ^ 2 := by
    rw [← hcardQ, div_add' _ _ _ hQpos.ne', le_div_iff₀ hQpos]
    nlinarith
  calc |w x| ≤ |w x - g x| + |g x| := by
        have := abs_sub_abs_le_abs_sub (w x) (g x)
        linarith
    _ ≤ L' + Real.sqrt (2 * A * M₂ / ((t : ℝ) + 1) ^ d + 2 * (d * t * L') ^ 2) :=
        add_le_add herr (Real.abs_le_sqrt hgx)

end Rigidity.Proofs.Regularity.GeneralDim
