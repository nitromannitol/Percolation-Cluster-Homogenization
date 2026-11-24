import PercolationClusterHomogenization.Proofs.Percolation.PlanarStripDuality

/-!
# Walks of faces crossing closed edges, in absolute coordinates

A walk of the square lattice is read as a walk of faces, the vertex `z` standing for the unit
square with lower-left corner `z`; a step from `z` to `z'` crosses the edge
`{sepLo z z', sepHi z z'}` separating the two faces. The separating edge commutes with
translations (`sepLo_add`, `sepHi_add`). In these coordinates:

* if the rectangle `c + [0, m] × [0, n]` has no open left-right crossing, there is a walk of faces
  in `[c₀, c₀ + m - 1] × [c₁ - 1, c₁ + n]` from the row `c₁ + n` to the row `c₁ - 1` all of whose
  steps cross closed edges (`exists_faceWalk_of_not_crossing`);
* such a walk of faces and an open left-right walk of the rectangle cross: some step of the walk of
  faces crosses an open edge (`exists_dart_open_of_crossing`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)
open Percolation.Literature (sepLo sepHi sepEdge)

variable {η : Configuration 2}

theorem sup_add_site (z z' c : Site 2) : (z + c) ⊔ (z' + c) = z ⊔ z' + c := by
  funext i
  simp only [Pi.add_apply, Pi.sup_apply]
  rcases le_total (z i) (z' i) with h | h
  · rw [sup_of_le_right (by linarith), sup_of_le_right h]
  · rw [sup_of_le_left (by linarith), sup_of_le_left h]

theorem sepLo_add (z z' c : Site 2) : sepLo (z + c) (z' + c) = sepLo z z' + c :=
  sup_add_site z z' c

theorem sepHi_add (z z' c : Site 2) : sepHi (z + c) (z' + c) = sepHi z z' + c := by
  unfold Percolation.Literature.sepHi
  rw [sup_add_site]
  by_cases h : z 0 = z' 0
  · have h' : (z + c) 0 = (z' + c) 0 := by simp only [Pi.add_apply, h]
    rw [if_pos h', if_pos h]
    abel
  · have h' : ¬ (z + c) 0 = (z' + c) 0 := by simp only [Pi.add_apply]; omega
    rw [if_neg h', if_neg h]
    abel

/-- The translation of the square lattice by `c`. -/
def latticeShift (c : Site 2) : zdGraph 2 →g zdGraph 2 where
  toFun z := z + c
  map_rel' h := (zdGraph_adj_add_iff c).2 h

theorem mem_vendorConfig_iff {c a b : Site 2} :
    s(a, b) ∈ vendorConfig η c ↔ (openGraph η).Adj (a + c) (b + c) :=
  ⟨adj_add_of_mem_vendorConfig, fun h => ⟨a, b, rfl, h⟩⟩

/-- **A walk of faces crossing only closed edges from the top to the bottom of a rectangle without
open left-right crossing.** -/
theorem exists_faceWalk_of_not_crossing {c : Site 2} {m n : ℕ}
    (h : ¬ ∃ a b, ReachIn η (latticeBox c m n) a b ∧ a 0 = c 0 ∧ b 0 = c 0 + m) :
    ∃ (t s : Site 2) (Q : (zdGraph 2).Walk t s), t 1 = c 1 + n ∧ s 1 = c 1 - 1 ∧
      (∀ z ∈ Q.support, c 0 ≤ z 0 ∧ z 0 + 1 ≤ c 0 + m ∧ c 1 - 1 ≤ z 1 ∧ z 1 ≤ c 1 + n) ∧
      ∀ d ∈ Q.darts, ¬ (openGraph η).Adj (sepLo d.fst d.snd) (sepHi d.fst d.snd) := by
  obtain ⟨t, s, Q, ht, hs, hQ, hd⟩ := exists_dualWalk_of_not_crossing h
  refine ⟨latticeShift c t, latticeShift c s, Q.map (latticeShift c),
    by change t 1 + c 1 = c 1 + n; rw [ht]; ring, by change s 1 + c 1 = c 1 - 1; rw [hs]; ring,
    fun z hz => ?_, fun d hdm hadj => ?_⟩
  · rw [SimpleGraph.Walk.support_map (latticeShift c) Q, List.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have := Percolation.Literature.mem_dualRectangle_iff.1 (hQ z₀ hz₀)
    change c 0 ≤ z₀ 0 + c 0 ∧ z₀ 0 + c 0 + 1 ≤ c 0 + m ∧ c 1 - 1 ≤ z₀ 1 + c 1 ∧
      z₀ 1 + c 1 ≤ c 1 + n
    omega
  · rw [SimpleGraph.Walk.darts_map (latticeShift c) Q, List.mem_map] at hdm
    obtain ⟨d₀, hd₀, rfl⟩ := hdm
    apply hd d₀ hd₀
    change (openGraph η).Adj (sepLo (d₀.fst + c) (d₀.snd + c))
      (sepHi (d₀.fst + c) (d₀.snd + c)) at hadj
    rw [sepLo_add, sepHi_add] at hadj
    exact mem_vendorConfig_iff.2 hadj

/-- **A walk of faces from the top to the bottom of a rectangle crosses every open left-right walk
of the rectangle**: one of its steps crosses an open edge. -/
theorem exists_dart_open_of_crossing {c a b : Site 2} {m n : ℕ} (W : (openGraph η).Walk a b)
    (hW : ∀ v ∈ W.support, v ∈ latticeBox c m n) (ha : a 0 = c 0) (hb : b 0 = c 0 + m)
    {t s : Site 2} (Q : (zdGraph 2).Walk t s)
    (hQ : ∀ z ∈ Q.support, c 0 ≤ z 0 ∧ z 0 + 1 ≤ c 0 + m ∧ c 1 - 1 ≤ z 1 ∧ z 1 ≤ c 1 + n)
    (ht : t 1 = c 1 + n) (hs : s 1 = c 1 - 1) :
    ∃ d ∈ Q.darts, (openGraph η).Adj (sepLo d.fst d.snd) (sepHi d.fst d.snd) := by
  set P := W.map (openToLattice η c) with hP
  set Q' := Q.map (latticeShift (-c)) with hQ'
  have hPs : ∀ z ∈ P.support, 0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    rw [hP, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    have := hW v hv
    simp only [latticeBox, Set.mem_setOf_eq] at this
    change 0 ≤ v 0 - c 0 ∧ v 0 - c 0 ≤ (m : ℤ) ∧ 0 ≤ v 1 - c 1 ∧ v 1 - c 1 ≤ (n : ℤ)
    omega
  have hQs : ∀ z ∈ Q'.support, 0 ≤ z 0 ∧ z 0 + 1 ≤ (m : ℤ) ∧ -1 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    rw [hQ', SimpleGraph.Walk.support_map (latticeShift (-c)) Q, List.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    have := hQ v hv
    change 0 ≤ v 0 + -c 0 ∧ v 0 + -c 0 + 1 ≤ (m : ℤ) ∧ -1 ≤ v 1 + -c 1 ∧ v 1 + -c 1 ≤ (n : ℤ)
    omega
  obtain ⟨d', hd', hmem⟩ := Percolation.Literature.exists_dart_sepEdge_mem_edges (M := m) (N := n)
    P Q' hPs hQs (by change a 0 - c 0 = 0; omega) (by change b 0 - c 0 = (m : ℤ); omega)
    (by change t 1 + -c 1 = (n : ℤ); omega) (by change s 1 + -c 1 = -1; omega)
  rw [hQ', SimpleGraph.Walk.darts_map (latticeShift (-c)) Q, List.mem_map] at hd'
  obtain ⟨d, hd, rfl⟩ := hd'
  refine ⟨d, hd, ?_⟩
  have hv := mem_vendorConfig_of_mem_edges_map W hmem
  change s(sepLo (d.fst + -c) (d.snd + -c), sepHi (d.fst + -c) (d.snd + -c)) ∈
    vendorConfig η c at hv
  rw [sepLo_add, sepHi_add, mem_vendorConfig_iff, neg_add_cancel_right,
    neg_add_cancel_right] at hv
  exact hv

end Rigidity.Percolation
