import PercolationClusterHomogenization.Proofs.Percolation.PlanarFaceWalks

/-!
# Level crossings and exits of walks of the square lattice

* A walk of the square lattice from a vertex with `k`-th coordinate at most `lo` to a vertex with
  `k`-th coordinate at least `hi ≥ lo` contains a piece from the level `lo` to the level `hi` whose
  `k`-th coordinates stay in `[lo, hi]` (`exists_levelCrossing`).
* A walk from a vertex of a set to a vertex outside it leaves the set along a step `p → q` after a
  piece inside the set (`exists_exit`).

The pieces are taken with their vertices and steps among those of the walk.
-/

open LatticeProb.Percolation

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)

theorem abs_sub_le_one_of_zdGraph_adj {z z' : Site 2} (h : (zdGraph 2).Adj z z') (k : Fin 2) :
    |z k - z' k| ≤ 1 := by
  rw [Percolation.Literature.zdGraph_two_adj_iff] at h
  rw [abs_le]
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk with rfl | rfl <;> constructor <;> omega

/-- The first arrival at the level `hi`. -/
theorem exists_prefix_level {k : Fin 2} {hi : ℤ} :
    ∀ {u v : Site 2} (W : (zdGraph 2).Walk u v), u k ≤ hi → hi ≤ v k →
      ∃ (v₁ : Site 2) (W₁ : (zdGraph 2).Walk u v₁), v₁ k = hi ∧
        (∀ z ∈ W₁.support, z k ≤ hi) ∧ (∀ z ∈ W₁.support, z ∈ W.support) ∧
        ∀ d ∈ W₁.darts, d ∈ W.darts
  | _, _, .nil, hu, hv => ⟨_, .nil, le_antisymm hu hv, fun z hz => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]; exact hu, fun z hz => hz, fun d hd => by simp at hd⟩
  | u, _, .cons h p, hu, hv => by
      by_cases hu' : u k = hi
      · exact ⟨u, .nil, hu', fun z hz => by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          rw [hz]; exact hu, fun z hz => by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          rw [hz]; exact SimpleGraph.Walk.start_mem_support _, fun d hd => by simp at hd⟩
      · have hw := abs_sub_le_one_of_zdGraph_adj h k
        rw [abs_le] at hw
        obtain ⟨v₁, W₁, h1, h2, h3, h4⟩ := exists_prefix_level p (by omega) hv
        refine ⟨v₁, .cons h W₁, h1, fun z hz => ?_, fun z hz => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.1 hz with rfl | hz
          · omega
          · exact h2 z hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact SimpleGraph.Walk.start_mem_support _
          · exact List.mem_cons_of_mem _ (h3 z hz)
        · rw [SimpleGraph.Walk.darts_cons] at hd ⊢
          rcases List.mem_cons.1 hd with rfl | hd
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons_of_mem _ (h4 d hd)

/-- The last departure from the level `lo`. -/
theorem exists_suffix_level {k : Fin 2} {lo : ℤ} :
    ∀ {u v : Site 2} (W : (zdGraph 2).Walk u v), lo ≤ v k → (∃ z ∈ W.support, z k ≤ lo) →
      ∃ (u₁ : Site 2) (W₂ : (zdGraph 2).Walk u₁ v), u₁ k = lo ∧
        (∀ z ∈ W₂.support, lo ≤ z k) ∧ (∀ z ∈ W₂.support, z ∈ W.support) ∧
        ∀ d ∈ W₂.darts, d ∈ W.darts
  | _, _, .nil, hv, ⟨z, hz, hzk⟩ => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact ⟨_, .nil, le_antisymm hzk hv, fun z' hz' => by
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz'
        rw [hz']; exact hv, fun z' hz' => hz', fun d hd => by simp at hd⟩
  | u, _, .cons h p, hv, ⟨z, hz, hzk⟩ => by
      by_cases hp : ∃ z ∈ p.support, z k ≤ lo
      · obtain ⟨u₁, W₂, h1, h2, h3, h4⟩ := exists_suffix_level p hv hp
        exact ⟨u₁, W₂, h1, h2, fun z hz => List.mem_cons_of_mem _ (h3 z hz), fun d hd => by
          rw [SimpleGraph.Walk.darts_cons]; exact List.mem_cons_of_mem _ (h4 d hd)⟩
      · push Not at hp
        have hzu : z = u := by
          rcases List.mem_cons.1 hz with rfl | hz
          · rfl
          · exact absurd hzk (not_le.2 (hp z hz))
        subst hzu
        have hw := abs_sub_le_one_of_zdGraph_adj h k
        rw [abs_le] at hw
        have hw' := hp _ (SimpleGraph.Walk.start_mem_support p)
        refine ⟨z, .cons h p, by omega, fun z' hz' => ?_, fun z' hz' => hz', fun d hd => hd⟩
        rcases List.mem_cons.1 hz' with rfl | hz'
        · omega
        · exact (hp z' hz').le

/-- **Level crossing.** A walk from the level `≤ lo` to the level `≥ hi` contains a piece from the
level `lo` to the level `hi` inside the slab `lo ≤ z k ≤ hi`. -/
theorem exists_levelCrossing {k : Fin 2} {lo hi : ℤ} (hlh : lo ≤ hi) {u v : Site 2}
    (W : (zdGraph 2).Walk u v) (hu : u k ≤ lo) (hv : hi ≤ v k) :
    ∃ (u₁ v₁ : Site 2) (W' : (zdGraph 2).Walk u₁ v₁), u₁ k = lo ∧ v₁ k = hi ∧
      (∀ z ∈ W'.support, lo ≤ z k ∧ z k ≤ hi) ∧ (∀ z ∈ W'.support, z ∈ W.support) ∧
      ∀ d ∈ W'.darts, d ∈ W.darts := by
  obtain ⟨v₁, W₁, h1, h2, h3, h4⟩ := exists_prefix_level W (hu.trans hlh) hv
  obtain ⟨u₁, W₂, g1, g2, g3, g4⟩ := exists_suffix_level W₁ (by rw [h1]; exact hlh)
    ⟨u, SimpleGraph.Walk.start_mem_support _, hu⟩
  exact ⟨u₁, v₁, W₂, g1, h1, fun z hz => ⟨g2 z hz, h2 z (g3 z hz)⟩,
    fun z hz => h3 z (g3 z hz), fun d hd => h4 d (g4 d hd)⟩

/-- **Exit.** A walk from a vertex of `B` to a vertex outside `B` has a piece inside `B` followed
by a step leaving `B`. -/
theorem exists_exit {B : Set (Site 2)} :
    ∀ {u v : Site 2} (W : (zdGraph 2).Walk u v), u ∈ B → v ∉ B →
      ∃ (p q : Site 2) (W₁ : (zdGraph 2).Walk u p) (h : (zdGraph 2).Adj p q),
        (∀ z ∈ W₁.support, z ∈ B) ∧ q ∉ B ∧
        (∀ z ∈ (W₁.concat h).support, z ∈ W.support) ∧ ∀ d ∈ (W₁.concat h).darts, d ∈ W.darts
  | _, _, .nil, hu, hv => absurd hu hv
  | u, _, .cons (v := w) h p, hu, hv => by
      by_cases hw : w ∈ B
      · obtain ⟨p', q, W₁, h', h1, h2, h3, h4⟩ := exists_exit p hw hv
        refine ⟨p', q, .cons h W₁, h', fun z hz => ?_, h2, fun z hz => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact hu
          · exact h1 z hz
        · rw [SimpleGraph.Walk.concat_cons, SimpleGraph.Walk.support_cons] at hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact SimpleGraph.Walk.start_mem_support _
          · exact List.mem_cons_of_mem _ (h3 z hz)
        · rw [SimpleGraph.Walk.concat_cons, SimpleGraph.Walk.darts_cons] at hd
          rw [SimpleGraph.Walk.darts_cons]
          rcases List.mem_cons.1 hd with rfl | hd
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons_of_mem _ (h4 d hd)
      · refine ⟨u, w, .nil, h, fun z hz => ?_, hw, fun z hz => ?_, fun d hd => ?_⟩
        · rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          rw [hz]; exact hu
        · rw [SimpleGraph.Walk.concat_nil, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil] at hz
          rw [SimpleGraph.Walk.support_cons]
          rcases List.mem_cons.1 hz with rfl | hz
          · exact List.mem_cons.2 (Or.inl rfl)
          · rw [List.mem_singleton] at hz
            rw [hz]
            exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _)
        · rw [SimpleGraph.Walk.concat_nil, SimpleGraph.Walk.darts_cons,
            SimpleGraph.Walk.darts_nil, List.mem_singleton] at hd
          rw [hd, SimpleGraph.Walk.darts_cons]
          exact List.mem_cons.2 (Or.inl rfl)

end Rigidity.Percolation
