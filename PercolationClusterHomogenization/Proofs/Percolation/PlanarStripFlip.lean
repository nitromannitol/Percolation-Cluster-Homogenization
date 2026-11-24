import PercolationClusterHomogenization.Proofs.Percolation.PlanarFaceSwap
import PercolationClusterHomogenization.Proofs.Percolation.PlanarWalkLevels

/-!
# Flipping one bond does not change the crossings of wide strips

Let `ω, ω'` be two configurations of `ℤ²` equal off a bond `e = {x, y}`, and let `S` be a square
`c₀ + [0, M]²` around `x` whose four outer strips of width `w` have open crossings in their long
directions in `ω`, with `x` at distance more than `w + 2` from the sides of `S`. Then a rectangle
`c + [0, m] × [0, n]` with `n ≥ M + 3` has an open left-right crossing in `ω` if and only if it has
one in `ω'` (`crossing_iff_of_flip`).

This is the first step of the proof of Lemma 3.5 of Dario for the planar partition of meshed cubes.
If one of the two configurations, `η`, has no
crossing while the other, `η'`, has one, planar duality gives a walk of faces of the rectangle from
its top to its bottom crossing only edges closed in `η` (`exists_faceWalk_of_not_crossing`). It
crosses the open crossing of `η'` (`exists_dart_open_of_crossing`), necessarily at the bond `e`. The
part of the walk of faces from the face next to `e` to an end of the walk outside `S` leaves `S`
through one of its sides and so crosses the corresponding outer strip of `S`; there it crosses the
open crossing of that strip, an edge open in `η` (`exists_levelCrossing`, `exists_exit`), which is
impossible (`false_of_flip_crossing`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)
open Percolation.Literature (sepLo sepHi)

/-- A walk of faces all of whose steps cross closed edges. -/
def FaceClosed (η : Configuration 2) {u v : Site 2} (W : (zdGraph 2).Walk u v) : Prop :=
  ∀ d ∈ W.darts, ¬ (openGraph η).Adj (sepLo d.fst d.snd) (sepHi d.fst d.snd)

theorem FaceClosed.mono {η : Configuration 2} {u v u' v' : Site 2} {W : (zdGraph 2).Walk u v}
    {W' : (zdGraph 2).Walk u' v'} (h : FaceClosed η W) (hW : ∀ d ∈ W'.darts, d ∈ W.darts) :
    FaceClosed η W' :=
  fun d hd => h d (hW d hd)

theorem FaceClosed.reverse {η : Configuration 2} {u v : Site 2} {W : (zdGraph 2).Walk u v}
    (h : FaceClosed η W) : FaceClosed η W.reverse := by
  intro d hd
  rw [SimpleGraph.Walk.darts_reverse, List.mem_reverse, List.mem_map] at hd
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  change ¬ (openGraph η).Adj (sepLo d₀.snd d₀.fst) (sepHi d₀.snd d₀.fst)
  rw [Percolation.Literature.sepLo_comm, Percolation.Literature.sepHi_comm]
  exact h d₀ hd₀

/-- Two configurations equal off a bond have the same open edges other than that bond. -/
theorem openGraph_adj_iff_of_agree_off {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {u v : Vertex 2} (huv : s(u, v) ≠ e.1) :
    (openGraph ω').Adj u v ↔ (openGraph ω).Adj u v := by
  have key : ∀ h : (nearestNeighborGraph 2).Adj u v, bondOfAdjacent h ≠ e := fun h hb =>
    huv (by rw [← hb]; rfl)
  constructor
  · rintro ⟨h, ho⟩
    exact ⟨h, by rw [← hagree _ (key h)]; exact ho⟩
  · rintro ⟨h, ho⟩
    exact ⟨h, by rw [hagree _ (key h)]; exact ho⟩

/-- Two configurations equal off a bond agree on the open edges inside a region not containing an
endpoint of the bond. -/
theorem adj_iff_of_agree_off_of_notMem {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {x y : Vertex 2} (hexy : e.1 = s(x, y))
    {S : Set (Vertex 2)} (hx : x ∉ S) :
    ∀ u ∈ S, ∀ v ∈ S, ((openGraph ω').Adj u v ↔ (openGraph ω).Adj u v) := by
  intro u hu v hv
  refine openGraph_adj_iff_of_agree_off hagree fun h => ?_
  rw [hexy] at h
  rcases Sym2.eq_iff.1 h with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact hx hu
  · exact hx hv

/-- An edge open in `η'` and closed in `η` is the flipped bond. -/
theorem eq_of_adj_of_not_adj {η η' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → η' b = η b) {u v : Vertex 2} (h' : (openGraph η').Adj u v)
    (h : ¬ (openGraph η).Adj u v) : s(u, v) = e.1 := by
  by_contra hne
  exact h ((openGraph_adj_iff_of_agree_off hagree hne).1 h')

/-- The faces on either side of an edge `{x, y}` are within distance two of `x`. -/
theorem abs_sub_le_two_of_sepEdge {z z' x y : Site 2} (hzz' : (zdGraph 2).Adj z z')
    (hxy : (zdGraph 2).Adj x y) (h : s(sepLo z z', sepHi z z') = s(x, y)) (i : Fin 2) :
    |z i - x i| ≤ 2 := by
  have hz := abs_sub_le_one_of_zdGraph_adj hzz' i
  have hx := abs_sub_le_one_of_zdGraph_adj hxy i
  have hlo : z i ≤ sepLo z z' i ∧ sepLo z z' i ≤ z i + 1 := by
    change z i ≤ max (z i) (z' i) ∧ max (z i) (z' i) ≤ z i + 1
    rw [abs_le] at hz
    constructor
    · exact le_max_left _ _
    · exact max_le (by omega) (by omega)
  rw [abs_le] at hz hx ⊢
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1] at hlo
    constructor <;> omega
  · rw [h1] at hlo
    constructor <;> omega

/-- The faces of the square `c₀ + [0, M]²`. -/
def faceSquare (c₀ : Site 2) (M : ℕ) : Set (Site 2) :=
  {z | c₀ 0 ≤ z 0 ∧ z 0 + 1 ≤ c₀ 0 + M ∧ c₀ 1 ≤ z 1 ∧ z 1 + 1 ≤ c₀ 1 + M}

/-- **A walk of faces crossing only closed edges cannot leave a square through its outer strips
of width `w` when these have open crossings.** -/
theorem false_of_exit_faceSquare {η : Configuration 2} {c₀ : Site 2} {M w : ℕ}
    (hT : ∃ a b, ReachIn η (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M)
    (hB : ∃ a b, ReachIn η (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M)
    (hL : ∃ a b, ReachIn η (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M)
    (hR : ∃ a b, ReachIn η (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M)
    {u v : Site 2} (A : (zdGraph 2).Walk u v) (hA : FaceClosed η A)
    (hu : ∀ i, c₀ i + w + 1 ≤ u i ∧ u i + w + 2 ≤ c₀ i + M) (hv : v ∉ faceSquare c₀ M) : False := by
  have huF : u ∈ faceSquare c₀ M := by
    have h0 := hu 0
    have h1 := hu 1
    exact ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨p, q, W₁, hpq, hW₁, hq, hsupp, hdarts⟩ := exists_exit A huF hv
  set V := W₁.concat hpq with hV
  have hVc : FaceClosed η V := hA.mono hdarts
  have hpF := hW₁ p W₁.end_mem_support
  have hVs : ∀ z ∈ V.support, z ∈ faceSquare c₀ M ∨ z = q := by
    intro z hz
    rw [hV, SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact Or.inl (hW₁ z hz)
    · exact Or.inr rfl
  have hpq' := hpq
  rw [Percolation.Literature.zdGraph_two_adj_iff] at hpq'
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := hpF
  have hu0 := hu 0
  have hu1 := hu 1
  have hside : q 0 = c₀ 0 - 1 ∨ q 0 = c₀ 0 + M ∨ q 1 = c₀ 1 - 1 ∨ q 1 = c₀ 1 + M := by
    simp only [faceSquare, Set.mem_setOf_eq, not_and_or, not_le] at hq
    omega
  rcases hside with hq0 | hq0 | hq1 | hq1
  · -- the left side: the walk crosses the left strip from right to left
    obtain ⟨aL, bL, ⟨WL, hWL⟩, haL, hbL⟩ := hL
    obtain ⟨u₁, v₁, W', hu₁, hv₁, hW's, hW'supp, hW'd⟩ :=
      exists_levelCrossing (k := 0) (lo := c₀ 0 - 1) (hi := c₀ 0 + w) (by omega) V.reverse
        (by omega) (by omega)
    obtain ⟨d, hd, hadj⟩ := exists_dart_open_of_vcrossing (c := c₀) (m := w) (n := M) WL hWL
      haL hbL W'.reverse (fun z hz => by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have hz' := hW'supp z hz
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
        have hb := hW's z hz
        rcases hVs z hz' with hF | rfl
        · obtain ⟨-, -, h3, h4⟩ := hF
          exact ⟨h3, h4, hb.1, hb.2⟩
        · exact ⟨by omega, by omega, hb.1, hb.2⟩)
      (by omega) (by omega)
    exact (hVc.reverse.mono hW'd).reverse d hd hadj
  · -- the right side
    obtain ⟨aR, bR, ⟨WR, hWR⟩, haR, hbR⟩ := hR
    obtain ⟨u₁, v₁, W', hu₁, hv₁, hW's, hW'supp, hW'd⟩ :=
      exists_levelCrossing (k := 0) (lo := c₀ 0 + M - w - 1) (hi := c₀ 0 + M) (by omega) V
        (by omega) (by omega)
    obtain ⟨d, hd, hadj⟩ := exists_dart_open_of_vcrossing (c := ![c₀ 0 + M - w, c₀ 1]) (m := w)
      (n := M) WR hWR (by change aR 1 = c₀ 1; exact haR) (by change bR 1 = c₀ 1 + M; exact hbR)
      W'.reverse (fun z hz => by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have hz' := hW'supp z hz
        have hb := hW's z hz
        change c₀ 1 ≤ z 1 ∧ z 1 + 1 ≤ c₀ 1 + M ∧ c₀ 0 + M - w - 1 ≤ z 0 ∧
          z 0 ≤ c₀ 0 + M - w + w
        rcases hVs z hz' with hF | rfl
        · obtain ⟨-, -, h3, h4⟩ := hF
          exact ⟨h3, h4, by omega, by omega⟩
        · exact ⟨by omega, by omega, by omega, by omega⟩)
      (by change v₁ 0 = c₀ 0 + M - w + w; rw [hv₁]; ring)
      (by change u₁ 0 = c₀ 0 + M - w - 1; rw [hu₁])
    exact (hVc.mono hW'd).reverse d hd hadj
  · -- the bottom side
    obtain ⟨aB, bB, ⟨WB, hWB⟩, haB, hbB⟩ := hB
    obtain ⟨u₁, v₁, W', hu₁, hv₁, hW's, hW'supp, hW'd⟩ :=
      exists_levelCrossing (k := 1) (lo := c₀ 1 - 1) (hi := c₀ 1 + w) (by omega) V.reverse
        (by omega) (by omega)
    obtain ⟨d, hd, hadj⟩ := exists_dart_open_of_crossing (c := c₀) (m := M) (n := w) WB hWB
      haB hbB W'.reverse (fun z hz => by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have hz' := hW'supp z hz
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
        have hb := hW's z hz
        rcases hVs z hz' with hF | rfl
        · obtain ⟨h1, h2, -, -⟩ := hF
          exact ⟨h1, h2, hb.1, hb.2⟩
        · exact ⟨by omega, by omega, hb.1, hb.2⟩)
      (by omega) (by omega)
    exact (hVc.reverse.mono hW'd).reverse d hd hadj
  · -- the top side
    obtain ⟨aT, bT, ⟨WT, hWT⟩, haT, hbT⟩ := hT
    obtain ⟨u₁, v₁, W', hu₁, hv₁, hW's, hW'supp, hW'd⟩ :=
      exists_levelCrossing (k := 1) (lo := c₀ 1 + M - w - 1) (hi := c₀ 1 + M) (by omega) V
        (by omega) (by omega)
    obtain ⟨d, hd, hadj⟩ := exists_dart_open_of_crossing (c := ![c₀ 0, c₀ 1 + M - w]) (m := M)
      (n := w) WT hWT (by change aT 0 = c₀ 0; exact haT) (by change bT 0 = c₀ 0 + M; exact hbT)
      W'.reverse (fun z hz => by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have hz' := hW'supp z hz
        have hb := hW's z hz
        change c₀ 0 ≤ z 0 ∧ z 0 + 1 ≤ c₀ 0 + M ∧ c₀ 1 + M - w - 1 ≤ z 1 ∧
          z 1 ≤ c₀ 1 + M - w + w
        rcases hVs z hz' with hF | rfl
        · obtain ⟨h1, h2, -, -⟩ := hF
          exact ⟨h1, h2, by omega, by omega⟩
        · exact ⟨by omega, by omega, by omega, by omega⟩)
      (by change v₁ 1 = c₀ 1 + M - w + w; rw [hv₁]; ring)
      (by change u₁ 1 = c₀ 1 + M - w - 1; rw [hu₁])
    exact (hVc.mono hW'd).reverse d hd hadj

/-- **One direction of the flip lemma.** -/
theorem false_of_flip_crossing {η η' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → η' b = η b) {x y : Vertex 2} (hexy : e.1 = s(x, y))
    {c₀ : Site 2} {M w : ℕ}
    (hT : ∃ a b, ReachIn η (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M)
    (hB : ∃ a b, ReachIn η (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M)
    (hL : ∃ a b, ReachIn η (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M)
    (hR : ∃ a b, ReachIn η (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M)
    (hx : ∀ i, c₀ i + w + 3 ≤ x i ∧ x i + w + 4 ≤ c₀ i + M)
    {c a b : Site 2} {m n : ℕ} (hn : M + 3 ≤ n)
    (hP : ReachIn η' (latticeBox c m n) a b) (ha : a 0 = c 0) (hb : b 0 = c 0 + m)
    (hno : ¬ ∃ a b, ReachIn η (latticeBox c m n) a b ∧ a 0 = c 0 ∧ b 0 = c 0 + m) : False := by
  obtain ⟨t, s, Q, ht, hs, hQ, hQd⟩ := exists_faceWalk_of_not_crossing hno
  have hQc : FaceClosed η Q := hQd
  obtain ⟨W, hW⟩ := hP
  obtain ⟨d, hd, hadj'⟩ := exists_dart_open_of_crossing W hW ha hb Q hQ ht hs
  have he := eq_of_adj_of_not_adj hagree hadj' (hQc d hd)
  rw [hexy] at he
  have hxy : (zdGraph 2).Adj x y := by
    obtain ⟨x', y', he', h1⟩ := e.property
    rw [hexy] at he'
    have hl : (nearestNeighborGraph 2).Adj x y := by
      rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact lattice_adj_iff_l1Dist.2 h1
      · exact (lattice_adj_iff_l1Dist.2 h1).symm
    exact (DualDecayRectangle.lattice_adj_iff_zdGraph_adj x y).1 hl
  have hz := abs_sub_le_two_of_sepEdge d.adj hxy he
  have hdeep : ∀ i, c₀ i + w + 1 ≤ d.fst i ∧ d.fst i + w + 2 ≤ c₀ i + M := by
    intro i
    have h1 := hx i
    have h2 := hz i
    rw [abs_le] at h2
    constructor <;> omega
  have hmem : d.fst ∈ Q.support := Q.dart_fst_mem_support_of_mem_darts hd
  by_cases htF : t ∈ faceSquare c₀ M
  · have hsF : s ∉ faceSquare c₀ M := by
      intro hsF
      obtain ⟨-, -, h1, -⟩ := hsF
      obtain ⟨-, -, -, h2⟩ := htF
      omega
    exact false_of_exit_faceSquare hT hB hL hR (Q.dropUntil d.fst hmem)
      (hQc.mono fun d' hd' => Q.darts_dropUntil_subset_darts hmem hd') hdeep hsF
  · exact false_of_exit_faceSquare hT hB hL hR (Q.takeUntil d.fst hmem).reverse
      (hQc.mono fun d' hd' => Q.darts_takeUntil_subset_darts hmem hd').reverse hdeep htF

end Rigidity.Percolation
