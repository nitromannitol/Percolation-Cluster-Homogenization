import PercolationClusterHomogenization.Proofs.Percolation.PlanarPartition
import PercolationClusterHomogenization.Percolation.TriadicInfluenceBounds
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSubcubes

/-!
# Changes of the planar partition from changes of meshed cubes near a vertex

Let `ω, ω'` be two configurations whose meshed cubes (of scale at least `7`) agree except for cubes
of side below `L` whose centre is within five side lengths of a vertex `x`
(`MeshedFlipBound ω ω' x L`). Then

* the good cubes agree except for cubes of side below `3L` near `x` (`MeshedFlipBound.good`);
* the stable cubes agree except for cubes of side below `3L` whose centre is within `39 L` of `x`,
  since every cube of the influence set of a cube `D` has scale at least that of `D` and centre
  within eight of its side lengths from that of `D` (`MeshedFlipBound.stable`);
* the stopping cubes agree except for cubes of side below `9L` whose centre is within `42 L` of `x`
  (`MeshedFlipBound.stopping`);
* the partition cubes of `ω` and `ω'` at a vertex `z` with `|z - x|_∞ ≥ 47 L` coincide: the larger
  of two different partition cubes at `z` would be a stopping cube for both configurations,
  contradicting the maximality of the smaller (`planarPartCube_eq_of_meshedFlipBound`).

This is the passage from the goodness of cubes to the partition in the proof of Lemma 3.5 of Dario
for the planar partition of meshed cubes, as in the proof of Proposition 2.1 of Armstrong and Dario.
-/

open LatticeProb.Percolation

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- The side of a triadic cube of positive scale is three times the side of its children. -/
theorem TriadicCube.side_eq_three_mul_side_child {d : ℕ} {Q : TriadicCube d} (hQ : 0 < Q.scale)
    (dg : Fin d → Fin 3) : Q.side = 3 * (Q.child dg).side := by
  change (3 : ℤ) ^ Q.scale = 3 * 3 ^ (Q.scale - 1)
  rw [← pow_succ', Nat.sub_add_cancel hQ]

/-- The centre of a child is within one side length of the child from the centre of the cube. -/
theorem TriadicCube.abs_center_child_sub_le {d : ℕ} {Q : TriadicCube d} (hQ : 0 < Q.scale)
    (dg : Fin d → Fin 3) (i : Fin d) :
    |(Q.child dg).center i - Q.center i| ≤ (Q.child dg).side := by
  have hs := Q.side_eq_three_mul_side_child hQ dg
  have h0 : (0 : ℤ) < (Q.child dg).side := pow_pos (by norm_num) _
  have hd : ((dg i : ℕ) : ℤ) ≤ 2 := by have := (dg i).isLt; omega
  have e : (Q.child dg).center i - Q.center i =
      (Q.child dg).side * (((dg i : ℕ) : ℤ) - 1) := by
    change (Q.child dg).side * (3 * Q.index i + ((dg i : ℕ) : ℤ) - 1) - Q.side * Q.index i = _
    rw [hs]
    ring
  rw [e, abs_mul, abs_of_pos h0]
  have h1 : |((dg i : ℕ) : ℤ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> omega
  calc (Q.child dg).side * |((dg i : ℕ) : ℤ) - 1| ≤ (Q.child dg).side * 1 :=
        mul_le_mul_of_nonneg_left h1 h0.le
    _ = (Q.child dg).side := mul_one _

/-- The meshed cubes of scale at least `7` of `ω` and `ω'` agree except for cubes of side below `L`
whose centre is within five side lengths of `x`. -/
def MeshedFlipBound (ω ω' : Configuration 2) (x : Vertex 2) (L : ℤ) : Prop :=
  ∀ A : TriadicCube 2, (A ∈ planarMeshedFamily ω' ↔ A ∈ planarMeshedFamily ω) ∨
    (A.side < L ∧ ∀ i, |A.center i - x i| ≤ 5 * A.side)

theorem MeshedFlipBound.symm {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L) :
    MeshedFlipBound ω' ω x L :=
  fun A => (h A).imp Iff.symm id

/-- **Changes of good cubes.** -/
theorem MeshedFlipBound.good {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L)
    (A : TriadicCube 2) :
    (A ∈ planarGoodCubes ω' ↔ A ∈ planarGoodCubes ω) ∨
      (A.side < 3 * L ∧ ∀ i, |A.center i - x i| ≤ 5 * A.side) := by
  by_cases hpos : 0 < A.scale
  · by_cases hall : (A ∈ planarMeshedFamily ω' ↔ A ∈ planarMeshedFamily ω) ∧
        ∀ dg, (A.child dg ∈ planarMeshedFamily ω' ↔ A.child dg ∈ planarMeshedFamily ω)
    · left
      unfold planarGoodCubes TriadicCube.goodOfWellConnected
      simp only [Set.mem_setOf_eq, hall.1, hall.2]
    · right
      have hA0 : (0 : ℤ) < A.side := pow_pos (by norm_num) _
      by_cases hA : A ∈ planarMeshedFamily ω' ↔ A ∈ planarMeshedFamily ω
      · obtain ⟨dg, hdg⟩ := not_forall.1 fun h' => hall ⟨hA, h'⟩
        rcases h (A.child dg) with h1 | ⟨h1, h2⟩
        · exact absurd h1 hdg
        · have hs := A.side_eq_three_mul_side_child hpos dg
          have hC0 : (0 : ℤ) < (A.child dg).side := pow_pos (by norm_num) _
          refine ⟨by rw [hs]; linarith, fun i => ?_⟩
          have hc := A.abs_center_child_sub_le hpos dg i
          have h2i := h2 i
          calc |A.center i - x i|
              ≤ |A.center i - (A.child dg).center i| + |(A.child dg).center i - x i| :=
                abs_sub_le _ _ _
            _ ≤ (A.child dg).side + 5 * (A.child dg).side := by
                rw [abs_sub_comm] at hc
                linarith
            _ ≤ 5 * A.side := by rw [hs]; linarith
      · rcases h A with h1 | ⟨h1, h2⟩
        · exact absurd h1 hA
        · exact ⟨by linarith, h2⟩
  · left
    have hno : ∀ ω₀ : Configuration 2, A ∉ planarGoodCubes ω₀ := fun ω₀ hA => hpos hA.1
    exact ⟨fun h1 => absurd h1 (hno ω'), fun h1 => absurd h1 (hno ω)⟩

/-- **Changes of stable cubes.** -/
theorem MeshedFlipBound.stable {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L)
    (D : TriadicCube 2) :
    (D ∈ TriadicCube.stableGood (planarGoodCubes ω') ↔
        D ∈ TriadicCube.stableGood (planarGoodCubes ω)) ∨
      (D.side < 3 * L ∧ ∀ i, |D.center i - x i| < 39 * L) := by
  by_cases hall : ∀ A ∈ D.influence, (A ∈ planarGoodCubes ω' ↔ A ∈ planarGoodCubes ω)
  · left
    unfold TriadicCube.stableGood
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h1 A hA => (hall A hA).1 (h1 hA), fun h1 A hA => (hall A hA).2 (h1 hA)⟩
  · right
    obtain ⟨A, hA⟩ := not_forall.1 hall
    obtain ⟨hAD, hne⟩ := Classical.not_imp.1 hA
    rcases h.good A with h1 | ⟨h1, h2⟩
    · exact absurd h1 hne
    · have hsc := TriadicCube.scale_le_of_mem_influence hAD
      have hside : D.side ≤ A.side := by
        change (3 : ℤ) ^ D.scale ≤ 3 ^ A.scale
        exact pow_le_pow_right₀ (by norm_num) hsc
      refine ⟨by linarith, fun i => ?_⟩
      have hcen := TriadicCube.abs_center_sub_le_of_mem_influence hAD i
      have h2i := h2 i
      calc |D.center i - x i| ≤ |D.center i - A.center i| + |A.center i - x i| :=
            abs_sub_le _ _ _
        _ ≤ 8 * A.side + 5 * A.side := add_le_add hcen h2i
        _ < 39 * L := by linarith

/-- **Changes of stopping cubes.** -/
theorem MeshedFlipBound.stopping {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L)
    (D : TriadicCube 2) :
    (D.IsStopping (planarGoodCubes ω') ↔ D.IsStopping (planarGoodCubes ω)) ∨
      (D.side < 9 * L ∧ ∀ i, |D.center i - x i| < 42 * L) := by
  have hD0 : (0 : ℤ) < D.side := pow_pos (by norm_num) _
  by_cases hpos : 0 < D.scale
  · by_cases hall : (D ∈ TriadicCube.stableGood (planarGoodCubes ω') ↔
          D ∈ TriadicCube.stableGood (planarGoodCubes ω)) ∧
        ∀ dg, (D.child dg ∈ TriadicCube.stableGood (planarGoodCubes ω') ↔
          D.child dg ∈ TriadicCube.stableGood (planarGoodCubes ω))
    · left
      unfold TriadicCube.IsStopping
      simp only [hall.1, hall.2]
    · right
      by_cases hDs : D ∈ TriadicCube.stableGood (planarGoodCubes ω') ↔
          D ∈ TriadicCube.stableGood (planarGoodCubes ω)
      · obtain ⟨dg, hdg⟩ := not_forall.1 fun h' => hall ⟨hDs, h'⟩
        rcases h.stable (D.child dg) with h1 | ⟨h1, h2⟩
        · exact absurd h1 hdg
        · have hs := D.side_eq_three_mul_side_child hpos dg
          refine ⟨by rw [hs]; linarith, fun i => ?_⟩
          have hc := D.abs_center_child_sub_le hpos dg i
          have h2i := h2 i
          rw [abs_sub_comm] at hc
          calc |D.center i - x i|
              ≤ |D.center i - (D.child dg).center i| + |(D.child dg).center i - x i| :=
                abs_sub_le _ _ _
            _ < 3 * L + 39 * L := by linarith
            _ = 42 * L := by ring
      · rcases h.stable D with h1 | ⟨h1, h2⟩
        · exact absurd h1 hDs
        · exact ⟨by linarith, fun i => by linarith [h2 i]⟩
  · have hz : D.scale = 0 := by omega
    have e : ∀ ω₀ : Configuration 2, D.IsStopping (planarGoodCubes ω₀) ↔
        D ∈ TriadicCube.stableGood (planarGoodCubes ω₀) := fun ω₀ =>
      ⟨fun h1 => h1.1, fun h1 => ⟨h1, Or.inl hz⟩⟩
    rw [e ω', e ω]
    rcases h.stable D with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨by linarith, fun i => by linarith [h2 i]⟩

/-- **The partition cubes away from the vertex coincide.** -/
theorem planarPartCube_eq_of_meshedFlipBound (hP : PlanarPartitionEvent ω)
    (hP' : PlanarPartitionEvent ω') {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L)
    {z : Vertex 2} (hz : ∃ i, 47 * L ≤ |z i - x i|) :
    planarPartCube ω' z = planarPartCube ω z := by
  have hkey : ∀ D : TriadicCube 2, z ∈ D.vertices →
      (D.IsStopping (planarGoodCubes ω') ↔ D.IsStopping (planarGoodCubes ω)) := by
    intro D hzD
    rcases h.stopping D with h1 | ⟨h1, h2⟩
    · exact h1
    · exfalso
      obtain ⟨i, hi⟩ := hz
      have hzc := TriadicCube.abs_sub_center_le hzD i
      have hside : D.side = 3 ^ D.scale := rfl
      have hD0 : (0 : ℤ) < D.side := pow_pos (by norm_num) _
      have h2i := h2 i
      have htri : |z i - x i| ≤ |z i - D.center i| + |D.center i - x i| := abs_sub_le _ _ _
      linarith
  obtain ⟨hzQ, hQ⟩ := planarPartCube_spec hP z
  obtain ⟨hzQ', hQ'⟩ := planarPartCube_spec hP' z
  rcases lt_trichotomy (planarPartCube ω z).scale (planarPartCube ω' z).scale with hlt | heq | hgt
  · exfalso
    have hQ'ω := (hkey _ hzQ').1 hQ'.1
    have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le hzQ hzQ' hlt.le
    have := hQ.2 _ hQ'ω hsub
    omega
  · exact (TriadicCube.eq_of_mem_of_scale_eq heq hzQ hzQ').symm
  · exfalso
    have hQω' := (hkey _ hzQ).2 hQ.1
    have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le hzQ' hzQ hgt.le
    have := hQ'.2 _ hQω' hsub
    omega

/-- **The partition cubes near a vertex are not much larger than the partition cube of the
vertex.** If `|z - x|_∞ ≤ M`, the partition cube of `z` has side at most
`3 max(size(□_𝒫(x)), M + 1)`: otherwise the triadic cube `G` of the scale below that of
`□_𝒫(z)` containing `x` lies in `□_𝒫(z)` or touches it, so that by the comparison of the scales of
neighbouring partition cubes the partition cube of a vertex of `G` contains `G`, hence `x`. -/
theorem side_planarPartCube_le_of_near (hP : PlanarPartitionEvent ω) {x z : Vertex 2} {M : ℤ}
    (hz : ∀ i, |z i - x i| ≤ M) :
    (planarPartCube ω z).side ≤ 3 * max (planarPartCube ω x).side (M + 1) := by
  obtain ⟨hzQ, hQ⟩ := planarPartCube_spec hP z
  have hk : 8 ≤ (planarPartCube ω z).scale := (planarPartCube_meshed hP z).2
  set Q := planarPartCube ω z with hQdef
  set s := (planarPartCube ω x).side with hs
  set k := Q.scale with hkdef
  have hxG0 : x ∈ (triadicCubeAt (k - 1) x).vertices := mem_triadicCubeAt (k - 1) x
  have hG0s : (triadicCubeAt (k - 1) x).scale = k - 1 := scale_triadicCubeAt (k - 1) x
  set G0 := triadicCubeAt (k - 1) x with hG0
  set t : ℤ := G0.side with ht
  have htpow : t = 3 ^ (k - 1) := by
    rw [ht]
    change (3 : ℤ) ^ G0.scale = _
    rw [hG0s]
  have hb : Q.side = 3 * t := by
    rw [htpow]
    change (3 : ℤ) ^ Q.scale = 3 * 3 ^ (k - 1)
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have ht0 : 0 < t := by rw [htpow]; positivity
  obtain ⟨h, hh⟩ : ∃ h : ℤ, t = 2 * h + 1 := by
    have hodd : Odd t := by rw [htpow]; exact Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, hm⟩
  have hh0 : 0 ≤ h := by linarith
  by_contra hlt
  push Not at hlt
  rw [hb] at hlt
  have hts : s < t := by have := le_max_left s (M + 1); linarith
  have htM : M + 1 < t := by have := le_max_right s (M + 1); linarith
  have hcQ : ∀ i, 2 * |z i - Q.center i| + 1 ≤ Q.side := fun i =>
    TriadicCube.abs_sub_center_le hzQ i
  have hcG : ∀ i, 2 * |x i - G0.center i| + 1 ≤ t := fun i =>
    TriadicCube.abs_sub_center_le hxG0 i
  have hdiff : ∀ i, G0.center i - Q.center i = t * (G0.index i - 3 * Q.index i) := fun i => by
    change G0.side * G0.index i - Q.side * Q.index i = _
    rw [hb]
    ring
  have hbound : ∀ i, |G0.index i - 3 * Q.index i| ≤ 2 := fun i => by
    have h1 := hz i
    rw [abs_sub_comm] at h1
    have h2 := hcQ i
    rw [hb] at h2
    have h3 := hcG i
    rw [abs_sub_comm] at h3
    have tri : |G0.center i - Q.center i| ≤
        |G0.center i - x i| + |x i - z i| + |z i - Q.center i| := by
      calc |G0.center i - Q.center i| ≤ |G0.center i - z i| + |z i - Q.center i| :=
            abs_sub_le _ _ _
        _ ≤ |G0.center i - x i| + |x i - z i| + |z i - Q.center i| := by
            have := abs_sub_le (G0.center i) (x i) (z i)
            linarith
    rw [hdiff i, abs_mul, abs_of_pos ht0] at tri
    have hlt3 : t * |G0.index i - 3 * Q.index i| < t * 3 := by linarith
    have := lt_of_mul_lt_mul_left hlt3 ht0.le
    have := Int.lt_iff_add_one_le.1 this
    linarith
  -- a vertex `v` of `G0` and a vertex `u` of `Q` at distance at most one
  set δ : Fin 2 → ℤ := fun i => G0.index i - 3 * Q.index i with hδ
  set v : Vertex 2 := fun i => if δ i = 2 then G0.center i - h
    else if δ i = -2 then G0.center i + h else G0.center i with hv
  set u : Vertex 2 := fun i => if δ i = 2 then Q.center i + (3 * h + 1)
    else if δ i = -2 then Q.center i - (3 * h + 1) else G0.center i with hu
  have hvG : v ∈ G0.vertices := by
    intro i
    have e : G0.side * G0.index i = G0.center i := rfl
    rw [e, ← ht]
    simp only [hv]
    split_ifs
    · rw [show 2 * (G0.center i - h - G0.center i) = -(2 * h) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
      linarith
    · rw [show 2 * (G0.center i + h - G0.center i) = 2 * h by ring, abs_of_nonneg (by linarith)]
      linarith
    · rw [sub_self, mul_zero, abs_zero]
      exact ht0
  have huQ : u ∈ Q.vertices := by
    intro i
    have e : Q.side * Q.index i = Q.center i := rfl
    rw [e, hb]
    simp only [hu]
    have hbi := hbound i
    split_ifs with h2 hm2
    · rw [show 2 * (Q.center i + (3 * h + 1) - Q.center i) = 6 * h + 2 by ring,
        abs_of_nonneg (by linarith)]
      linarith
    · rw [show 2 * (Q.center i - (3 * h + 1) - Q.center i) = -(6 * h + 2) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
      linarith
    · have hd1 : |δ i| ≤ 1 := by
        have h2' : δ i ≠ 2 := h2
        have hm2' : δ i ≠ -2 := hm2
        have hbi' : |δ i| ≤ 2 := hbi
        rw [abs_le] at hbi' ⊢
        constructor <;> omega
      rw [show 2 * (G0.center i - Q.center i) = 2 * (t * δ i) by rw [hdiff i], abs_mul,
        abs_mul, abs_two, abs_of_pos ht0]
      have : t * |δ i| ≤ t * 1 := mul_le_mul_of_nonneg_left hd1 ht0.le
      linarith
  have hnear : ∀ i, |v i - u i| ≤ 1 := by
    intro i
    simp only [hv, hu]
    have hd := hdiff i
    split_ifs with h2 hm2
    · have e1 : G0.center i - h - (Q.center i + (3 * h + 1)) = 1 := by
        have e2 : G0.center i - h - (Q.center i + (3 * h + 1)) = t * δ i - 4 * h - 1 := by
          rw [← hd]; ring
        rw [e2, h2, hh]
        ring
      rw [e1]
      norm_num
    · have e1 : G0.center i + h - (Q.center i - (3 * h + 1)) = -1 := by
        have e2 : G0.center i + h - (Q.center i - (3 * h + 1)) = t * δ i + 4 * h + 1 := by
          rw [← hd]; ring
        rw [e2, hm2, hh]
        ring
      rw [e1]
      norm_num
    · rw [sub_self, abs_zero]
      norm_num
  -- the partition cube of `v` contains `G0`, hence `x`
  have hcu : planarPartCube ω u = Q := planarPartCube_eq_of_mem hP huQ
  obtain ⟨hvC, hvS⟩ := planarPartCube_spec hP v
  have hQu := hQ.1
  rw [← hcu] at hQu
  have hsc := (hvS.1.scales_close_of_near hQu hvC (by rw [hcu]; exact huQ) hnear).2
  rw [hcu] at hsc
  have hG0sub : G0.vertices ⊆ (planarPartCube ω v).vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hvG hvC (by rw [hG0s]; omega)
  have hcell : planarPartCube ω x = planarPartCube ω v := planarPartCube_eq_of_mem hP (hG0sub hxG0)
  have hside : t ≤ (planarPartCube ω v).side := by
    rw [ht]
    change (3 : ℤ) ^ G0.scale ≤ 3 ^ (planarPartCube ω v).scale
    exact pow_le_pow_right₀ (by norm_num) (by rw [hG0s]; omega)
  have hsv : s = (planarPartCube ω v).side := by rw [hs, hcell]
  linarith

/-- **The partition cubes near the vertex are not much larger** (second configuration). -/
theorem side_planarPartCube_le_of_meshedFlipBound (hP : PlanarPartitionEvent ω)
    (hP' : PlanarPartitionEvent ω') {x : Vertex 2} {L : ℤ} (h : MeshedFlipBound ω ω' x L)
    {M : ℤ} {z : Vertex 2} (hz : ∀ i, |z i - x i| ≤ M) :
    (planarPartCube ω' z).side ≤ max (9 * L) (3 * max (planarPartCube ω x).side (M + 1)) := by
  obtain ⟨hzQ', hQ'⟩ := planarPartCube_spec hP' z
  obtain ⟨hzQ, hQ⟩ := planarPartCube_spec hP z
  rcases h.stopping (planarPartCube ω' z) with h1 | ⟨h1, -⟩
  · have hQ'ω := h1.1 hQ'.1
    have hsc : (planarPartCube ω' z).scale ≤ (planarPartCube ω z).scale := by
      by_contra hlt
      push Not at hlt
      have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le hzQ hzQ' hlt.le
      have := hQ.2 _ hQ'ω hsub
      omega
    have hle : (planarPartCube ω' z).side ≤ (planarPartCube ω z).side := by
      change (3 : ℤ) ^ (planarPartCube ω' z).scale ≤ 3 ^ (planarPartCube ω z).scale
      exact pow_le_pow_right₀ (by norm_num) hsc
    exact le_max_of_le_right (hle.trans (side_planarPartCube_le_of_near hP hz))
  · exact le_max_of_le_left h1.le

end Rigidity.Percolation
