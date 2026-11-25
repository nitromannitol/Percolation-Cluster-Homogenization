import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZero
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseTransfer
import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicDist
import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicApproximationCubes

/-!
# Passing between a cluster function and its coarsening on the balls of `ℤᵈ`

The steps of the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2) which compare a
function `u` on an open cluster `C` of `ℤᵈ` with its coarsening `[u]_𝒫` (`partitionCoarse C u`, the
value at the anchor of the partition cube), for the partition into good cubes in every dimension:

* the anchors of the partition cubes lie in the infinite cluster
  (`partitionAnchor_mem_uniqueInfiniteComponent`), each anchor is the anchor of at most
  `size(□)^d` points (`card_filter_partitionAnchor_eq_le`), and an anchor is within the side of
  its cube of each point of the cube (`abs_partitionAnchor_sub_lt`);
* a lattice ball of radius `ρ ≥ 2 √d` has at least `(ρ / (2 √d))^d` points
  (`le_card_latticeBallD`);
* if the anchors of the points of `B_ρ` lie in `C ∩ B_R` and the partition cubes there have sides
  at most `S`, `‖[u]_𝒫 - a‖_{L̲²(B_ρ)} ≤ (S^d (2√d)^d R^d / ρ^d)^{1/2} ‖u - a‖_R`
  (`componentBallL2_coarse_sub_const_leD`, the crude bound of the top coarse oscillation), with
  `‖·‖_R = R^{-d/2} ‖·‖_{ℓ²(C ∩ B_R)}`;
* if moreover `|W(z̄) - W(y)| ≤ Λ ∑ᵢ |z̄ᵢ - yᵢ|`,
  `∑_{B_ρ} |[u]_𝒫 - W| ≤ (∑_{B_ρ} 3^{d s})^{1/2} ‖u - W‖_{ℓ²(C ∩ B_R)} + d Λ ∑_{B_ρ} 3^{s}`
  (`sum_abs_coarse_sub_leD`, the `ℓ¹` step of Step 2 of the proof, by Cauchy–Schwarz over the
  fibres of the anchor map), `s` the scales of the partition cubes.

These are the planar statements of `PlanarCoarseTransfer` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-! ### The anchors of the partition cubes -/

/-- The anchors of the partition cubes lie in the infinite cluster. -/
theorem partitionAnchor_mem_uniqueInfiniteComponent (hd : 0 < d) (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (x : Vertex d) :
    partitionAnchor ω x ∈ (uniqueInfiniteComponent h).supp :=
  (mem_uniqueInfiniteComponent_iff h _).2 (infinite_supp_partitionAnchor hd hP x)

/-- Each anchor is the anchor of at most `size(□)^d` points. -/
theorem card_filter_partitionAnchor_eq_le (hP : PartitionEvent ω) (B : Finset (Vertex d))
    (x : Vertex d) :
    ((B.filter fun x' => partitionAnchor ω x' = partitionAnchor ω x).card : ℝ) ≤
      ((3 : ℝ) ^ (partitionCube ω x).scale) ^ d := by
  classical
  have hle : (B.filter fun x' => partitionAnchor ω x' = partitionAnchor ω x) ⊆
      (partitionCube ω x).toIntegerCube.vertices := by
    intro y hy
    obtain ⟨-, hyz⟩ := mem_filter.1 hy
    have h1 : partitionAnchor ω x ∈ (partitionCube ω y).vertices := by
      rw [← hyz]; exact partitionAnchor_mem hP y
    have h2 := partitionCube_eq_of_mem hP h1
    have h3 := partitionCube_eq_of_mem hP (partitionAnchor_mem hP x)
    rw [TriadicCube.mem_toIntegerCube_vertices, ← h3, h2]
    exact mem_partitionCube hP y
  have hcard := card_le_card hle
  rw [IntegerCube.card_vertices_eq] at hcard
  have h1 : ((B.filter fun x' => partitionAnchor ω x' = partitionAnchor ω x).card : ℝ) ≤
      (((partitionCube ω x).toIntegerCube.size ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
  have h2 : (((partitionCube ω x).toIntegerCube.size ^ d : ℕ) : ℝ) =
      ((3 : ℝ) ^ (partitionCube ω x).scale) ^ d := by
    change (((3 ^ (partitionCube ω x).scale : ℕ) ^ d : ℕ) : ℝ) = _
    push_cast; rfl
  rw [h2] at h1
  exact h1

/-- An anchor is within the side of its cube of each coordinate of the point. -/
theorem abs_partitionAnchor_sub_le (hP : PartitionEvent ω) (y : Vertex d) (k : Fin d) :
    |((partitionAnchor ω y k : ℤ) : ℝ) - ((y k : ℤ) : ℝ)| ≤ (3 : ℝ) ^ (partitionCube ω y).scale := by
  have h := abs_sub_lt_side_of_mem (partitionAnchor_mem hP y) (mem_partitionCube hP y) k
  have h' : ((|partitionAnchor ω y k - y k| : ℤ) : ℝ) ≤ ((3 : ℤ) ^ (partitionCube ω y).scale : ℤ) := by
    exact_mod_cast h.le
  push_cast at h'
  exact h'

/-! ### Lattice balls -/

/-- The points of `ℤᵈ` in the lattice ball. -/
noncomputable def latticeBallPointsD [NeZero d] (z : Vertex d) (ρ : ℝ) : Finset (Vertex d) :=
  (componentEuclideanBall (latticeComponent d) z ρ).image Subtype.val

theorem mem_latticeBallPointsD [NeZero d] {z y : Vertex d} {ρ : ℝ} :
    y ∈ latticeBallPointsD z ρ ↔
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < ρ := by
  rw [latticeBallPointsD, mem_image_componentEuclideanBall]
  exact ⟨fun h => h.2, fun h => ⟨mem_latticeComponent_supp y, h⟩⟩

theorem sum_latticeBallPointsD [NeZero d] (z : Vertex d) (ρ : ℝ) (f : Vertex d → ℝ) :
    ∑ x ∈ componentEuclideanBall (latticeComponent d) z ρ, f x.val =
      ∑ y ∈ latticeBallPointsD z ρ, f y :=
  (sum_image (f := f) fun _ _ _ _ h => Subtype.val_injective h).symm

theorem card_latticeBallPointsD [NeZero d] (z : Vertex d) (ρ : ℝ) :
    (latticeBallPointsD z ρ).card = (componentEuclideanBall (latticeComponent d) z ρ).card :=
  card_image_of_injective _ Subtype.val_injective

/-- A sum over a finite set of points of a cluster inside a ball is at most the sum over the
cluster ball. -/
theorem sum_le_sum_componentEuclideanBallD (C : OpenComponent ω) {S : Finset (Vertex d)}
    {R : ℝ} (hS : ∀ y ∈ S, y ∈ C.supp ∧
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R)
    (f : Vertex d → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ y ∈ S, f y ≤ ∑ x ∈ componentEuclideanBall C 0 R, f x.val := by
  classical
  rw [← sum_image (f := f) (s := componentEuclideanBall C 0 R)
    fun _ _ _ _ h => Subtype.val_injective h]
  exact sum_le_sum_of_subset_of_nonneg (fun y hy => (mem_image_componentEuclideanBall C 0 y R).2
    (hS y hy)) fun y _ _ => hf y

/-- **A lattice ball of radius `ρ ≥ 2 √d` has at least `(ρ / (2 √d))^d` points.** -/
theorem le_card_latticeBallD [NeZero d] (z : Vertex d) {ρ : ℝ} (hρ : 2 * Real.sqrt d ≤ ρ) :
    (ρ / (2 * Real.sqrt d)) ^ d ≤
      ((componentEuclideanBall (latticeComponent d) z ρ).card : ℝ) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  set L := ⌊ρ / (2 * Real.sqrt d)⌋₊ with hL
  have hL1 : ρ / (2 * Real.sqrt d) - 1 < L := Nat.sub_one_lt_floor _
  have hLle : (L : ℝ) ≤ ρ / (2 * Real.sqrt d) := Nat.floor_le (by positivity)
  have hsub : supBox z L ⊆ latticeBallPointsD z ρ := by
    intro y hy
    rw [mem_latticeBallPointsD]
    refine (dist_le_of_mem_supBox hy).trans_lt ?_
    have : Real.sqrt d * L ≤ Real.sqrt d * (ρ / (2 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hLle hsd.le
    have e : Real.sqrt d * (ρ / (2 * Real.sqrt d)) = ρ / 2 := by field_simp
    linarith
  have hcard : (supBox z L).card = (2 * L + 1) ^ d := by
    rw [supBox, Fintype.card_piFinset]
    simp only [Int.card_Icc]
    have : ∀ i : Fin d, (z i + (L : ℤ) + 1 - (z i - L)).toNat = 2 * L + 1 := fun i => by omega
    simp [this]
  have h := card_le_card hsub
  rw [hcard, card_latticeBallPointsD] at h
  have h' : ((2 * L + 1 : ℕ) : ℝ) ^ d ≤
      ((componentEuclideanBall (latticeComponent d) z ρ).card : ℝ) := by exact_mod_cast h
  have h2 : ρ / (2 * Real.sqrt d) ≤ ((2 * L + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact (pow_le_pow_left₀ (by positivity) h2 d).trans h'

/-! ### The coarsening on lattice balls -/

/-- **Crude bound for the coarse oscillation.** -/
theorem componentBallL2_coarse_sub_const_leD [NeZero d] (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ) {ρ R S : ℝ}
    (hρ : 2 * Real.sqrt d ≤ ρ) (hR : 0 < R) (hS : 0 ≤ S)
    (hanchor : ∀ y ∈ latticeBallPointsD 0 ρ,
      dist (latticeEuclideanEmbedding (partitionAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex d)) < R)
    (hsize : ∀ y ∈ latticeBallPointsD 0 ρ, (3 : ℝ) ^ (partitionCube ω y).scale ≤ S)
    (a : ℝ) :
    componentBallL2 (latticeComponent d) 0 ρ
        (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val - a) ≤
      Real.sqrt (S ^ d * (2 * Real.sqrt d) ^ d * R ^ d / ρ ^ d) *
        clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  set f : Vertex d → ℝ := fun y => Rigidity.Section3.extend (uniqueInfiniteComponent h) u y - a
    with hf
  have hsum1 : ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 ρ,
      (partitionCoarse (uniqueInfiniteComponent h) u x.val - a) ^ 2 =
      ∑ y ∈ latticeBallPointsD 0 ρ, f (partitionAnchor ω y) ^ 2 := by
    rw [sum_latticeBallPointsD 0 ρ
      (fun y => (partitionCoarse (uniqueInfiniteComponent h) u y - a) ^ 2)]
    rfl
  have hfib := sum_sq_comp_le (latticeBallPointsD 0 ρ) (partitionAnchor ω) (W₀ := S ^ d) f
    fun y hy => (card_filter_partitionAnchor_eq_le hP _ y).trans
      (pow_le_pow_left₀ (by positivity) (hsize y hy) d)
  have himage : ∑ y ∈ (latticeBallPointsD 0 ρ).image (partitionAnchor ω), f y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, f x.val ^ 2 := by
    refine sum_le_sum_componentEuclideanBallD (uniqueInfiniteComponent h) (fun y hy => ?_) _
      fun _ => sq_nonneg _
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact ⟨partitionAnchor_mem_uniqueInfiniteComponent hd hP h x, hanchor x hx⟩
  have hcl : ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, f x.val ^ 2 =
      R ^ d * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) ^ 2 := by
    rw [clusterBallVolumeL2, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity))]
    have e : ∀ x : (uniqueInfiniteComponent h),
        f x.val ^ 2 = ((u - fun _ => a : uniqueInfiniteComponent h → ℝ) x) ^ 2 := fun x => by
      simp only [hf, extend_val_of_mem, Pi.sub_apply]
    rw [sum_congr rfl fun x _ => e x]
    field_simp
  have hcard := le_card_latticeBallD 0 hρ
  have hcpos : (0 : ℝ) < ((componentEuclideanBall (latticeComponent d) 0 ρ).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hcard
  have hK : 0 ≤ Real.sqrt (S ^ d * (2 * Real.sqrt d) ^ d * R ^ d / ρ ^ d) *
      clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [componentBallL2, Real.sqrt_le_left hK, div_le_iff₀ hcpos, hsum1, mul_pow,
    Real.sq_sqrt (by positivity)]
  set D := clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)
  calc ∑ y ∈ latticeBallPointsD 0 ρ, f (partitionAnchor ω y) ^ 2
      ≤ S ^ d * ∑ y ∈ (latticeBallPointsD 0 ρ).image (partitionAnchor ω), f y ^ 2 := hfib
    _ ≤ S ^ d * (R ^ d * D ^ 2) :=
        mul_le_mul_of_nonneg_left (himage.trans hcl.le) (by positivity)
    _ = S ^ d * (2 * Real.sqrt d) ^ d * R ^ d / ρ ^ d * D ^ 2 * (ρ / (2 * Real.sqrt d)) ^ d := by
        rw [div_pow]; field_simp
    _ ≤ S ^ d * (2 * Real.sqrt d) ^ d * R ^ d / ρ ^ d * D ^ 2 *
          ((componentEuclideanBall (latticeComponent d) 0 ρ).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)

/-- **The `ℓ¹` step**: Cauchy–Schwarz over the fibres of the anchor map and the Lipschitz bound
of `W`. -/
theorem sum_abs_coarse_sub_leD [NeZero d] (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    (W : Vertex d → ℝ) {ρ R Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hanchor : ∀ y ∈ latticeBallPointsD 0 ρ,
      dist (latticeEuclideanEmbedding (partitionAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex d)) < R)
    (hLip : ∀ y ∈ latticeBallPointsD 0 ρ, |W (partitionAnchor ω y) - W y| ≤
      Λ * ∑ i, |((partitionAnchor ω y i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|) :
    ∑ y ∈ latticeBallPointsD 0 ρ, |partitionCoarse (uniqueInfiniteComponent h) u y - W y| ≤
      Real.sqrt (∑ y ∈ latticeBallPointsD 0 ρ, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d) *
          Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (u x - W x.val) ^ 2) +
        d * Λ * ∑ y ∈ latticeBallPointsD 0 ρ, (3 : ℝ) ^ (partitionCube ω y).scale := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set f : Vertex d → ℝ := fun y => Rigidity.Section3.extend (uniqueInfiniteComponent h) u y - W y
    with hf
  have hsplit : ∀ y, |partitionCoarse (uniqueInfiniteComponent h) u y - W y| ≤
      |f (partitionAnchor ω y)| + |W (partitionAnchor ω y) - W y| := fun y => by
    have e : partitionCoarse (uniqueInfiniteComponent h) u y - W y =
        f (partitionAnchor ω y) + (W (partitionAnchor ω y) - W y) := by
      simp only [hf, partitionCoarse]; ring
    rw [e]; exact abs_add_le _ _
  have h1 := sq_sum_abs_comp_le (latticeBallPointsD 0 ρ) (partitionAnchor ω)
    (fun y => ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d) f
    fun y _ => card_filter_partitionAnchor_eq_le hP _ y
  have himage : ∑ y ∈ (latticeBallPointsD 0 ρ).image (partitionAnchor ω), f y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, (u x - W x.val) ^ 2 := by
    have := sum_le_sum_componentEuclideanBallD (uniqueInfiniteComponent h)
      (S := (latticeBallPointsD 0 ρ).image (partitionAnchor ω)) (R := R) (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exact ⟨partitionAnchor_mem_uniqueInfiniteComponent hd hP h x, hanchor x hx⟩)
      (fun y => f y ^ 2) fun _ => sq_nonneg _
    refine this.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    simp only [hf, extend_val_of_mem]
  have hA0 : 0 ≤ ∑ y ∈ latticeBallPointsD 0 ρ, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d :=
    sum_nonneg fun _ _ => by positivity
  have hfirst : ∑ y ∈ latticeBallPointsD 0 ρ, |f (partitionAnchor ω y)| ≤
      Real.sqrt (∑ y ∈ latticeBallPointsD 0 ρ, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d) *
        Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
          (u x - W x.val) ^ 2) := by
    rw [← Real.sqrt_mul hA0]
    apply Real.le_sqrt_of_sq_le
    exact h1.trans (mul_le_mul_of_nonneg_left himage hA0)
  have hsecond : ∑ y ∈ latticeBallPointsD 0 ρ, |W (partitionAnchor ω y) - W y| ≤
      d * Λ * ∑ y ∈ latticeBallPointsD 0 ρ, (3 : ℝ) ^ (partitionCube ω y).scale := by
    rw [mul_sum]
    refine sum_le_sum fun y hy => (hLip y hy).trans ?_
    have hb : ∑ i, |((partitionAnchor ω y i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤
        d * (3 : ℝ) ^ (partitionCube ω y).scale := by
      calc _ ≤ ∑ _i : Fin d, (3 : ℝ) ^ (partitionCube ω y).scale :=
            sum_le_sum fun i _ => abs_partitionAnchor_sub_le hP y i
        _ = d * (3 : ℝ) ^ (partitionCube ω y).scale := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc Λ * ∑ i, |((partitionAnchor ω y i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|
        ≤ Λ * (d * (3 : ℝ) ^ (partitionCube ω y).scale) := mul_le_mul_of_nonneg_left hb hΛ
      _ = d * Λ * (3 : ℝ) ^ (partitionCube ω y).scale := by ring
  calc ∑ y ∈ latticeBallPointsD 0 ρ, |partitionCoarse (uniqueInfiniteComponent h) u y - W y|
      ≤ ∑ y ∈ latticeBallPointsD 0 ρ,
          (|f (partitionAnchor ω y)| + |W (partitionAnchor ω y) - W y|) :=
        sum_le_sum fun y _ => hsplit y
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add hfirst hsecond

end Rigidity.Proofs.Regularity
