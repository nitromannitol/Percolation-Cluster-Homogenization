import PercolationClusterHomogenization.Proofs.Percolation.PlanarLocality

/-!
# The anchor of a meshed cube depends only on the open edges inside the cube

The anchor `Q.planarAnchor ω` of a triadic cube `Q` of side `s ≥ 1000` is a vertex of `Q` joined
inside `Q` to every open walk in `Q` of span at least `⌊s/100⌋` in some coordinate, and joined
inside the square `9Q` of side `9s` to every such walk in `9Q`. When `Q` is meshed, the second
condition follows from the first (`TriadicCube.isPlanarAnchor_iff_of_meshed`): a long crossing of
`Q` reaches the hub of the strip mesh of `9Q`, which is joined to every long walk in `9Q`. Hence the
anchor of a cube meshed in two configurations depends only on the open edges inside the cube
(`TriadicCube.planarAnchor_eq_of_adj_iff_vertices`). This is the anchor step of the proof of
Lemma 3.5 of Dario for the planar partition of meshed cubes.
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- **The condition in `9Q` of the anchor of a meshed cube follows from the condition in `Q`.** -/
theorem TriadicCube.isPlanarAnchor_iff_of_meshed {Q : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) (a : Vertex 2) :
    Q.IsPlanarAnchor ω a ↔ a ∈ Q.vertices ∧
      ∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω Q.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω Q.vertices a c := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨ha, hQa⟩ => ⟨ha, hQa, ?_⟩⟩
  set w := 3 ^ Q.scale / 100 with hwdef
  have hQm := hQ _ Q.toIntegerCube_mem_planarSquares
  have hNm := hQ _ Q.ninefold_mem_planarSquares
  have hwQ : w + 1 ≤ Q.toIntegerCube.size := by change w + 1 ≤ 3 ^ Q.scale; omega
  have hwN : w + 1 ≤ Q.ninefold.size := by change w + 1 ≤ 9 * 3 ^ Q.scale; omega
  obtain ⟨a', -, -, hfaces⟩ := hQm.exists_hub hwQ
  obtain ⟨b, -, hbabs, -⟩ := hNm.exists_hub hwN
  have hQset := Q.coe_toIntegerCube_vertices
  obtain ⟨⟨yl, -, hylf, hayl⟩, ⟨yu, -, hyuf, hayu⟩⟩ := hfaces 0
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hcross : ReachIn ω Q.vertices yl yu := by
    rw [← hQset]
    exact hayl.symm.trans hayu
  have hdisp : yl 0 + (w : ℤ) ≤ yu 0 := by
    have : (Q.toIntegerCube.size : ℤ) = 3 ^ Q.scale := by
      change ((3 ^ Q.scale : ℕ) : ℤ) = _; push_cast; ring
    have hw100 : 100 * (w : ℤ) ≤ 3 ^ Q.scale := by
      have := Nat.mul_div_le (3 ^ Q.scale) 100
      have h' : ((100 * w : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at h'
      linarith
    omega
  have hQN := Q.vertices_subset_ninefold
  have hayl' : ReachIn ω Q.vertices a yl := hQa yl yu 0 hcross hdisp
  have hbyl : ReachIn ω ↑Q.ninefold.vertices b yl := hbabs yl yu 0 (hcross.mono hQN) hdisp
  intro c d k hcd hk
  exact ((hayl'.mono hQN).trans hbyl.symm).trans (hbabs c d k hcd hk)

/-- **The anchor of a cube meshed in two configurations depends only on the open edges inside the
cube.** -/
theorem TriadicCube.planarAnchor_eq_of_adj_iff_vertices {Q : TriadicCube 2}
    (hQ : Q.planarMeshed ω) (hQ' : Q.planarMeshed ω')
    (hagree : ∀ x ∈ Q.vertices, ∀ y ∈ Q.vertices,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) :
    Q.planarAnchor ω' = Q.planarAnchor ω := by
  unfold TriadicCube.planarAnchor
  by_cases hs : 1000 ≤ 3 ^ Q.scale
  · rw [if_pos ⟨hQ', hs⟩, if_pos ⟨hQ, hs⟩]
    have h1 : ∀ c d, ReachIn ω' Q.vertices c d ↔ ReachIn ω Q.vertices c d :=
      reachIn_iff_of_adj_iff hagree
    have hp : (fun e => Q.IsPlanarAnchor ω' (Q.center + e)) =
        fun e => Q.IsPlanarAnchor ω (Q.center + e) := by
      funext e
      rw [Q.isPlanarAnchor_iff_of_meshed hQ' hs, Q.isPlanarAnchor_iff_of_meshed hQ hs]
      simp only [h1]
    rw [hp]
  · rw [if_neg fun h => hs h.2, if_neg fun h => hs h.2]

end Rigidity.Percolation
