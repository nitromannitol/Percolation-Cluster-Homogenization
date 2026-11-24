import PercolationClusterHomogenization.Proofs.Percolation.PlanarLocality
import PercolationClusterHomogenization.Proofs.Percolation.Kesten.DualDecayRectangle

/-!
# Planar duality for the crossings of translated rectangles of a bond configuration

For a configuration `η` of `ℤ²` and a translation `c`, `vendorConfig η c` is the set of edges `{x, y}`
of the square lattice such that `{x + c, y + c}` is open. Open walks of `η` inside the rectangle
`c + [0, m] × [0, n]` and open walks of `vendorConfig η c` inside `[0, m] × [0, n]` correspond by the
translation (`lrCrossing_vendorConfig_of_reachIn`, `reachIn_of_walk_vendorConfig`). By planar duality
(`Percolation.Literature.lrCrossing_xor_dualTBCrossing_holds`), if the rectangle has no open
left-right crossing then there is a walk of faces from the top of its dual rectangle to the bottom
whose steps cross only closed edges (`exists_dualWalk_of_not_crossing`); such a walk meets every
left-right lattice walk of the rectangle at a step crossing one of its edges
(`Percolation.Literature.exists_dart_sepEdge_mem_edges`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)

variable {η : Configuration 2}

/-- Open edges are edges of the square lattice. -/
theorem zdGraph_adj_of_openGraph_adj {x y : Vertex 2} (h : (openGraph η).Adj x y) :
    (zdGraph 2).Adj x y :=
  (DualDecayRectangle.lattice_adj_iff_zdGraph_adj x y).1 (openGraph_le η h)

/-- The square lattice is invariant under translations. -/
theorem zdGraph_adj_add_iff {x y : Site 2} (c : Site 2) :
    (zdGraph 2).Adj (x + c) (y + c) ↔ (zdGraph 2).Adj x y := by
  rw [Percolation.Literature.zdGraph_two_adj_iff, Percolation.Literature.zdGraph_two_adj_iff]
  simp only [Pi.add_apply]
  constructor <;> intro h <;> omega

/-- The translation by `-c`, from the open graph of `η` to the square lattice. -/
def openToLattice (η : Configuration 2) (c : Site 2) : openGraph η →g zdGraph 2 where
  toFun v := v - c
  map_rel' {x y} h := by
    rw [← zdGraph_adj_add_iff c, sub_add_cancel, sub_add_cancel]
    exact zdGraph_adj_of_openGraph_adj h

/-- The edges `{x, y}` of the square lattice with `{x + c, y + c}` open in `η`. -/
def vendorConfig (η : Configuration 2) (c : Site 2) : Percolation.Literature.BondConfig (Site 2) :=
  {e | ∃ x y, e = s(x, y) ∧ (openGraph η).Adj (x + c) (y + c)}

theorem vendorConfig_subset (η : Configuration 2) (c : Site 2) :
    vendorConfig η c ⊆ (zdGraph 2).edgeSet := by
  rintro e ⟨x, y, rfl, h⟩
  rw [SimpleGraph.mem_edgeSet, ← zdGraph_adj_add_iff c]
  exact zdGraph_adj_of_openGraph_adj h

theorem adj_add_of_mem_vendorConfig {c a b : Site 2} (h : s(a, b) ∈ vendorConfig η c) :
    (openGraph η).Adj (a + c) (b + c) := by
  obtain ⟨x, y, hxy, hadj⟩ := h
  rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm

theorem mem_vendorConfig_of_adj {c u v : Site 2} (h : (openGraph η).Adj u v) :
    s(u - c, v - c) ∈ vendorConfig η c :=
  ⟨u - c, v - c, rfl, by rw [sub_add_cancel, sub_add_cancel]; exact h⟩

/-- The rectangle `c + [0, m] × [0, n]`. -/
def latticeBox (c : Site 2) (m n : ℕ) : Set (Vertex 2) :=
  {v | c 0 ≤ v 0 ∧ v 0 ≤ c 0 + m ∧ c 1 ≤ v 1 ∧ v 1 ≤ c 1 + n}

theorem sub_mem_rectangle_iff {c v : Site 2} {m n : ℕ} :
    v - c ∈ Percolation.Literature.rectangle m n ↔ v ∈ latticeBox c m n := by
  rw [Percolation.Literature.mem_rectangle_iff]
  simp only [latticeBox, Set.mem_setOf_eq, Pi.sub_apply]
  constructor <;> intro h <;> omega

/-- The edges of the translate of an open walk are in `vendorConfig`. -/
theorem mem_vendorConfig_of_mem_edges_map {c x y : Site 2} (W : (openGraph η).Walk x y)
    {e : Sym2 (Site 2)} (he : e ∈ (W.map (openToLattice η c)).edges) : e ∈ vendorConfig η c := by
  rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  have hset := W.edges_subset_edgeSet he'
  induction e' using Sym2.ind with
  | h u v =>
    rw [Sym2.map_mk]
    exact mem_vendorConfig_of_adj hset

/-- **An open left-right crossing of a translated rectangle gives a left-right crossing of
`vendorConfig`.** -/
theorem lrCrossing_vendorConfig_of_reachIn {c a b : Site 2} {m n : ℕ}
    (h : ReachIn η (latticeBox c m n) a b) (ha : a 0 = c 0) (hb : b 0 = c 0 + m) :
    vendorConfig η c ∈ Percolation.Literature.lrCrossing m n := by
  obtain ⟨W, hW⟩ := h
  have hsupp : ∀ z ∈ (W.map (openToLattice η c)).support,
      z ∈ (↑(Percolation.Literature.rectangle m n) : Set (Site 2)) := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact Finset.mem_coe.2 (sub_mem_rectangle_iff.2 (hW v hv))
  refine ⟨a - c, ?_, b - c, ?_, Percolation.Literature.mem_openConnIn_of_walk
    (W.map (openToLattice η c)) hsupp fun e he => mem_vendorConfig_of_mem_edges_map W he⟩
  · refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨sub_mem_rectangle_iff.2 (hW a W.start_mem_support), ?_⟩)
    simp [ha]
  · refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨sub_mem_rectangle_iff.2 (hW b W.end_mem_support), ?_⟩)
    simp [hb]

/-- **A lattice walk with edges in `vendorConfig` translates to an open walk.** -/
theorem reachIn_of_walk_vendorConfig {c : Site 2} {S : Set (Vertex 2)} {u v : Site 2}
    (p : (zdGraph 2).Walk u v) (hS : ∀ z ∈ p.support, z + c ∈ S)
    (hω : ∀ e ∈ p.edges, e ∈ vendorConfig η c) : ReachIn η S (u + c) (v + c) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, fun z hz => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact hS _ (by simp)⟩
  | @cons a b w hab p ih =>
    have hadj : (openGraph η).Adj (a + c) (b + c) :=
      adj_add_of_mem_vendorConfig (hω s(a, b) (by simp))
    obtain ⟨W, hW⟩ := ih (fun z hz => hS z (by simp [hz])) (fun e he => hω e (by simp [he]))
    refine ⟨SimpleGraph.Walk.cons hadj W, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hS a (by simp)
    · exact hW z hz

/-- **Planar duality for a translated rectangle.** If `c + [0, m] × [0, n]` has no open left-right
crossing, there is a walk of faces of the dual rectangle from its top side to its bottom side
whose steps cross only closed edges. -/
theorem exists_dualWalk_of_not_crossing {c : Site 2} {m n : ℕ}
    (h : ¬ ∃ a b, ReachIn η (latticeBox c m n) a b ∧ a 0 = c 0 ∧ b 0 = c 0 + m) :
    ∃ (t s : Site 2) (Q : (zdGraph 2).Walk t s), t 1 = n ∧ s 1 = -1 ∧
      (∀ z ∈ Q.support, z ∈ Percolation.Literature.dualRectangle m n) ∧
      ∀ d ∈ Q.darts, Percolation.Literature.sepEdge d.fst d.snd ∉ vendorConfig η c := by
  rcases Percolation.Literature.lrCrossing_xor_dualTBCrossing_holds m n (vendorConfig_subset η c)
    with ⟨hlr, -⟩ | ⟨hd, -⟩
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hlr
    obtain ⟨p, hpS, hpω⟩ :=
      Percolation.Literature.exists_walk_of_mem_openConnIn (vendorConfig_subset η c) hxy
    simp only [Finset.mem_coe, Percolation.Literature.leftSide,
      Percolation.Literature.rightSide, Finset.mem_filter] at hx hy
    refine h ⟨x + c, y + c, reachIn_of_walk_vendorConfig p (fun z hz => ?_) hpω, ?_, ?_⟩
    · have := hpS z hz
      rw [Finset.mem_coe] at this
      rw [← sub_mem_rectangle_iff (c := c), add_sub_cancel_right]
      exact this
    · rw [Pi.add_apply, hx.2, zero_add]
    · rw [Pi.add_apply, hy.2]
      ring
  · obtain ⟨t, ht, s, hs, hts⟩ := Percolation.Literature.mem_openCrossing_iff.1 hd
    obtain ⟨Q, hQS, hQω⟩ := Percolation.Literature.exists_walk_of_mem_openConnIn
      (fun _ h => h.1 : Percolation.Literature.dualConfig (vendorConfig η c) ⊆
        (zdGraph 2).edgeSet) hts
    simp only [Finset.mem_coe, Percolation.Literature.dualTopSide,
      Percolation.Literature.dualBottomSide, Finset.mem_filter] at ht hs
    refine ⟨t, s, Q, ht.2, hs.2, fun z hz => Finset.mem_coe.1 (hQS z hz), fun d hd' hsep => ?_⟩
    have hedge : s(d.fst, d.snd) ∈ Q.edges := by
      unfold SimpleGraph.Walk.edges
      exact List.mem_map_of_mem hd'
    have hdual := (Percolation.Literature.mem_dualConfig_iff.1 (hQω _ hedge)).2 _ hsep
    exact hdual (Percolation.Literature.dualEdge_sepEdge d.adj)

end Rigidity.Percolation
