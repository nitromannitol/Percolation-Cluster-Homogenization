import PercolationClusterHomogenization.External.WellConnected

/-!
# Cubes and open paths in cubes

A lattice step changes each coordinate by at most one; the open graph inside a set is a subgraph of
the open graph, and its walks starting in the set stay in it; the cube `z + Q_r` as a finset; and
the summability of stretched exponentials over the integers.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- A lattice step changes each coordinate by at most one. -/
theorem abs_coord_sub_le_one_of_adj {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y)
    (k : Fin d) : |y k - x k| ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := Graph.Zd.adj_iff.mp h <;> subst hi <;>
    by_cases hk : k = i <;> simp [unit, hk]

/-- The open graph inside `B` is a subgraph of the open graph. -/
theorem openIn_le (ω : Configuration d) (B : Set (Vertex d)) : openIn ω B ≤ openGraph ω :=
  fun _ _ h => h.1

/-- A walk of open edges inside `B` that starts in `B` stays in `B`. -/
theorem mem_of_mem_support_openIn {ω : Configuration d} {B : Set (Vertex d)} {a b : Vertex d}
    (p : (openIn ω B).Walk a b) (ha : a ∈ B) : ∀ v ∈ p.support, v ∈ B := by
  induction p with
  | nil => simpa using ha
  | cons h q ih =>
    intro v hv
    rcases (SimpleGraph.Walk.mem_support_iff _).mp hv with rfl | hv
    · exact ha
    · exact ih h.2.2 v hv

/-- The cube `z + Q_r` as a finset. -/
noncomputable def cubeFinset (z : Vertex d) (r : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (z i - r) (z i + r)

theorem mem_cubeFinset {z y : Vertex d} {r : ℕ} : y ∈ cubeFinset z r ↔ y ∈ cubeAt z r := by
  simp only [cubeFinset, Fintype.mem_piFinset, Finset.mem_Icc, cubeAt, Set.mem_setOf_eq, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

theorem card_cubeFinset (z : Vertex d) (r : ℕ) : (cubeFinset z r).card = (2 * r + 1) ^ d := by
  rw [cubeFinset, Fintype.card_piFinset,
    Finset.prod_congr rfl (g := fun _ => 2 * r + 1) (fun i _ => by rw [Int.card_Icc]; omega)]
  simp

theorem finite_cubeAt (z : Vertex d) (r : ℕ) : (cubeAt z r).Finite :=
  (cubeFinset z r).finite_toSet.subset fun _ hy => mem_cubeFinset.mpr hy

/-- A stretched exponential is summable over the integers. -/
theorem summable_exp_neg_mul_rpow {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Summable fun N : ℕ => Real.exp (-(c * (N : ℝ) ^ s)) := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have h := ((isLittleO_exp_neg_mul_rpow_atTop hc (-2 / s)).comp_tendsto hlim).isBigO
  refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
    (h.congr (fun N => by simp only [Function.comp, neg_mul]) (fun N => ?_))
  simp only [Function.comp]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

end Rigidity.Proofs.S3
