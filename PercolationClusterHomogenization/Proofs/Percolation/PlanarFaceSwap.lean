import PercolationClusterHomogenization.Proofs.Percolation.PlanarFaceWalks
import PercolationClusterHomogenization.Proofs.Lattice.Reflection

/-!
# The exchange of the coordinates and walks of faces

The exchange `σ` of the two coordinates of `ℤ²` maps faces to faces (lower-left corners to
lower-left corners) and the edge separating two adjacent faces to the edge separating their images
(`sepLo_siteSwap`, `sepHi_siteSwap`). With the action of `σ` on configurations, the crossing of a
left-right open walk and a top-bottom walk of faces gives the crossing of a top-bottom open walk and
a right-left walk of faces (`exists_dart_open_of_vcrossing`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)
open Percolation.Literature (sepLo sepHi)

/-- The exchange of the two coordinates. -/
def siteSwap (z : Site 2) : Site 2 := fun i => z (Equiv.swap 0 1 i)

@[simp] theorem siteSwap_zero (z : Site 2) : siteSwap z 0 = z 1 := by
  simp [siteSwap]

@[simp] theorem siteSwap_one (z : Site 2) : siteSwap z 1 = z 0 := by
  simp [siteSwap]

theorem zdGraph_adj_siteSwap_iff {z z' : Site 2} :
    (zdGraph 2).Adj (siteSwap z) (siteSwap z') ↔ (zdGraph 2).Adj z z' := by
  rw [Percolation.Literature.zdGraph_two_adj_iff, Percolation.Literature.zdGraph_two_adj_iff]
  simp only [siteSwap_zero, siteSwap_one]
  constructor <;> intro h <;> omega

/-- The exchange of the coordinates, as a map of the square lattice. -/
def siteSwapHom : zdGraph 2 →g zdGraph 2 where
  toFun := siteSwap
  map_rel' h := zdGraph_adj_siteSwap_iff.2 h

theorem sepLo_siteSwap (z z' : Site 2) :
    sepLo (siteSwap z) (siteSwap z') = siteSwap (sepLo z z') := rfl

theorem sepHi_siteSwap {z z' : Site 2} (h : (zdGraph 2).Adj z z') :
    sepHi (siteSwap z) (siteSwap z') = siteSwap (sepHi z z') := by
  rw [Percolation.Literature.zdGraph_two_adj_iff] at h
  have key : ((siteSwap z) 0 = (siteSwap z') 0) ↔ ¬ (z 0 = z' 0) := by
    simp only [siteSwap_zero]
    constructor <;> intro h' <;> omega
  unfold Percolation.Literature.sepHi
  by_cases h0 : z 0 = z' 0
  · rw [if_neg (fun h' => (key.1 h') h0), if_pos h0]
    funext i
    fin_cases i <;> simp [siteSwap]
  · rw [if_pos (key.2 h0), if_neg h0]
    funext i
    fin_cases i <;> simp [siteSwap]

/-- The exchange of the coordinates as an automorphism of the lattice. -/
abbrev swapIso : nearestNeighborGraph 2 ≃g nearestNeighborGraph 2 :=
  Rigidity.Proofs.S3.signedPermIso (Equiv.swap 0 1) 1

theorem swapIso_apply (x : Vertex 2) : swapIso x = siteSwap x := by
  funext i
  simp [Rigidity.Proofs.S3.signedPermIso, Rigidity.Proofs.S3.signedPermVertex, siteSwap]

/-- **A walk of faces from the right to the left of a rectangle crosses every open top-bottom walk
of the rectangle.** -/
theorem exists_dart_open_of_vcrossing {η : Configuration 2} {c a b : Site 2} {m n : ℕ}
    (W : (openGraph η).Walk a b) (hW : ∀ v ∈ W.support, v ∈ latticeBox c m n)
    (ha : a 1 = c 1) (hb : b 1 = c 1 + n) {t s : Site 2} (Q : (zdGraph 2).Walk t s)
    (hQ : ∀ z ∈ Q.support, c 1 ≤ z 1 ∧ z 1 + 1 ≤ c 1 + n ∧ c 0 - 1 ≤ z 0 ∧ z 0 ≤ c 0 + m)
    (ht : t 0 = c 0 + m) (hs : s 0 = c 0 - 1) :
    ∃ d ∈ Q.darts, (openGraph η).Adj (sepLo d.fst d.snd) (sepHi d.fst d.snd) := by
  set ηs := Rigidity.Proofs.S3.configurationMap swapIso η with hηs
  set W' := W.map (Rigidity.Proofs.S3.openGraphMap swapIso η).toRelEmbedding.toRelHom with hW'
  have hsupp : ∀ v ∈ W'.support, v ∈ latticeBox (siteSwap c) n m := by
    intro v hv
    rw [hW', SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have := hW u hu
    simp only [latticeBox, Set.mem_setOf_eq] at this ⊢
    rw [show (Rigidity.Proofs.S3.openGraphMap swapIso η).toRelEmbedding.toRelHom u = siteSwap u
      from swapIso_apply u]
    simp only [siteSwap_zero, siteSwap_one]
    omega
  obtain ⟨d', hd', hadj⟩ := exists_dart_open_of_crossing (η := ηs) (c := siteSwap c) (m := n)
    (n := m) W' hsupp
    (by change swapIso a 0 = siteSwap c 0; rw [swapIso_apply, siteSwap_zero, siteSwap_zero, ha])
    (by change swapIso b 0 = siteSwap c 0 + n; rw [swapIso_apply, siteSwap_zero, siteSwap_zero, hb])
    (Q.map siteSwapHom)
    (by
      intro z hz
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      have := hQ u hu
      change siteSwap c 0 ≤ siteSwap u 0 ∧ siteSwap u 0 + 1 ≤ siteSwap c 0 + n ∧
        siteSwap c 1 - 1 ≤ siteSwap u 1 ∧ siteSwap u 1 ≤ siteSwap c 1 + m
      simp only [siteSwap_zero, siteSwap_one]
      omega)
    (by change siteSwap t 1 = siteSwap c 1 + m; rw [siteSwap_one, siteSwap_one, ht])
    (by change siteSwap s 1 = siteSwap c 1 - 1; rw [siteSwap_one, siteSwap_one, hs])
  rw [SimpleGraph.Walk.darts_map, List.mem_map] at hd'
  obtain ⟨d, hd, rfl⟩ := hd'
  refine ⟨d, hd, ?_⟩
  change (openGraph ηs).Adj (sepLo (siteSwap d.fst) (siteSwap d.snd))
    (sepHi (siteSwap d.fst) (siteSwap d.snd)) at hadj
  rw [sepLo_siteSwap, sepHi_siteSwap d.adj, ← swapIso_apply, ← swapIso_apply] at hadj
  exact (Rigidity.Proofs.S3.openGraph_adj_configurationMap_iff swapIso η _ _).1 hadj

end Rigidity.Percolation
