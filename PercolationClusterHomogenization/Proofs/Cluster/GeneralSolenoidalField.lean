import PercolationClusterHomogenization.Proofs.Cluster.GeneralEdgePairing

/-!
# A bounded divergence-free lattice field equal to a coordinate direction on a cube, in every dimension

Step 1 of the proof of Lemma 5.7 of Armstrong and Dario takes, for a unit direction `e`, a smooth
compactly supported divergence-free continuum field equal to `e` on `[-1, 1]^d` (from the proof of
Lemma 3.2 of Armstrong and Smart) and discretizes it. We construct instead an exactly
divergence-free lattice field. For a coordinate direction `e_k` and an index `l ≠ k`, let
`ψ(z) = z_l χ_n(z)`, where `χ_n` is a cutoff equal to `1` on `{|z|_∞ ≤ 3ⁿ}` and to `0` on
`{|z|_∞ ≥ (5/4) 3ⁿ}` with slope `4 · 3⁻ⁿ`, and let the field be the discrete curl of `ψ` in the
plane of the coordinates `k, l`:
the flow through the edge `(x, x + e_k)` is `ψ(x) - ψ(x - e_l)`, through `(x, x + e_l)` it is
`ψ(x - e_k) - ψ(x)`, and it vanishes on the other edges (`cubeSolenoidalField`). This is the field
`G_i = ∑_j D_j^- A_{ij}` of an antisymmetric potential `A`, with `A_{kl} = -A_{lk} = ψ` and the
other entries zero; it is exactly divergence free (`sum_cubeSolenoidalField_sub_eq_zero`), equals
`e_k` on the edges near `□_n` (`cubeSolenoidalField_eq_single`), is bounded by `10`
(`abs_cubeSolenoidalField_le`) and vanishes on the edges not inside `□_{n+1}`. By summation by
parts its pairing with the gradient of any function over the edges of `□_{n+1}` vanishes
(`latticeEdgePairing_cubeSolenoidalField_eq_zero`): this is display (5.28) of Armstrong and Dario
with right side `0`. The two-dimensional version is `Rigidity.Percolation.solenoidalField`.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- The sup norm `|z|_∞` of a vertex of `ℤᵈ`, as a real number. -/
noncomputable def vertexSupNorm (z : Vertex d) : ℝ :=
  ((Finset.univ.sup fun i => (z i).natAbs : ℕ) : ℝ)

theorem vertexSupNorm_nonneg (z : Vertex d) : 0 ≤ vertexSupNorm z := Nat.cast_nonneg _

theorem abs_le_vertexSupNorm (z : Vertex d) (i : Fin d) : |(z i : ℝ)| ≤ vertexSupNorm z := by
  have h : (z i).natAbs ≤ Finset.univ.sup fun i => (z i).natAbs :=
    Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)
  have h' : ((z i).natAbs : ℝ) ≤ vertexSupNorm z := by
    unfold vertexSupNorm
    exact_mod_cast h
  rwa [Nat.cast_natAbs, Int.cast_abs] at h'

theorem vertexSupNorm_le_iff {z : Vertex d} {r : ℕ} :
    vertexSupNorm z ≤ r ↔ ∀ i, (z i).natAbs ≤ r := by
  unfold vertexSupNorm
  rw [Nat.cast_le, Finset.sup_le_iff]
  simp

theorem unit_apply_self (i : Fin d) : (unit i : Vertex d) i = 1 := by
  simp [unit]

theorem unit_apply_ne {i j : Fin d} (h : j ≠ i) : (unit i : Vertex d) j = 0 := by
  simp [unit, h]

/-- Moving by a unit vector changes the sup norm by at most one. -/
theorem vertexSupNorm_sub_unit_le (z : Vertex d) (i : Fin d) :
    vertexSupNorm (z - unit i) ≤ vertexSupNorm z + 1 ∧
      vertexSupNorm z ≤ vertexSupNorm (z - unit i) + 1 := by
  have key : ∀ (a b : Vertex d), (∀ j, (a j).natAbs ≤ (b j).natAbs + 1) →
      vertexSupNorm a ≤ vertexSupNorm b + 1 := by
    intro a b hab
    set r := Finset.univ.sup fun j => (b j).natAbs with hr
    have hb : vertexSupNorm b = r := rfl
    have h : vertexSupNorm a ≤ ((r + 1 : ℕ) : ℝ) := by
      refine vertexSupNorm_le_iff.2 fun j => (hab j).trans ?_
      exact Nat.add_le_add_right (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ j)) 1
    rw [hb]
    exact_mod_cast h
  have hz : ∀ j, (z - unit i) j = z j - (unit i : Vertex d) j := fun j => rfl
  constructor
  · refine key _ _ fun j => ?_
    rw [hz]
    by_cases hj : j = i
    · subst hj
      rw [unit_apply_self]
      omega
    · rw [unit_apply_ne hj, sub_zero]
      omega
  · refine key _ _ fun j => ?_
    rw [hz]
    by_cases hj : j = i
    · subst hj
      rw [unit_apply_self]
      omega
    · rw [unit_apply_ne hj, sub_zero]
      omega

theorem abs_vertexSupNorm_sub_unit_sub_le (z : Vertex d) (i : Fin d) :
    |vertexSupNorm z - vertexSupNorm (z - unit i)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := vertexSupNorm_sub_unit_le z i
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The cutoff `χ_n`, equal to `1` on `{|z|_∞ ≤ 3ⁿ}` and to `0` on `{|z|_∞ ≥ (5/4) 3ⁿ}`. -/
noncomputable def cubeCutoff (n : ℕ) (z : Vertex d) : ℝ :=
  max 0 (min 1 (5 - 4 * vertexSupNorm z / 3 ^ n))

theorem cubeCutoff_nonneg (n : ℕ) (z : Vertex d) : 0 ≤ cubeCutoff n z := le_max_left _ _

theorem cubeCutoff_le_one (n : ℕ) (z : Vertex d) : cubeCutoff n z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cubeCutoff_eq_one {n : ℕ} {z : Vertex d} (hz : vertexSupNorm z ≤ 3 ^ n) :
    cubeCutoff n z = 1 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have : 1 ≤ 5 - 4 * vertexSupNorm z / 3 ^ n := by
    rw [le_sub_comm, div_le_iff₀ h3]
    linarith
  rw [cubeCutoff, min_eq_left this, max_eq_right zero_le_one]

theorem cubeCutoff_eq_zero {n : ℕ} {z : Vertex d} (hz : 5 / 4 * 3 ^ n ≤ vertexSupNorm z) :
    cubeCutoff n z = 0 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have : 5 - 4 * vertexSupNorm z / 3 ^ n ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ h3]
    linarith
  rw [cubeCutoff, max_eq_left ((min_le_right _ _).trans this)]

theorem abs_cubeCutoff_sub_le (n : ℕ) (z z' : Vertex d) :
    |cubeCutoff n z - cubeCutoff n z'| ≤ 4 * |vertexSupNorm z - vertexSupNorm z'| / 3 ^ n := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (5 - 4 * vertexSupNorm z / 3 ^ n)) 0
    (min 1 (5 - 4 * vertexSupNorm z' / 3 ^ n))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (5 - 4 * vertexSupNorm z / 3 ^ n) 1
    (5 - 4 * vertexSupNorm z' / 3 ^ n)
  simp only [sub_self, abs_zero] at h1 h2
  have e : |5 - 4 * vertexSupNorm z / 3 ^ n - (5 - 4 * vertexSupNorm z' / 3 ^ n)| =
      4 * |vertexSupNorm z - vertexSupNorm z'| / 3 ^ n := by
    rw [show 5 - 4 * vertexSupNorm z / 3 ^ n - (5 - 4 * vertexSupNorm z' / 3 ^ n) =
      -(4 / 3 ^ n) * (vertexSupNorm z - vertexSupNorm z') by field_simp; ring, abs_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 4 / 3 ^ n)]
    ring
  rw [e] at h2
  unfold cubeCutoff
  have h0 : 0 ≤ 4 * |vertexSupNorm z - vertexSupNorm z'| / 3 ^ n := by positivity
  calc _ ≤ max 0 |min 1 (5 - 4 * vertexSupNorm z / 3 ^ n) -
        min 1 (5 - 4 * vertexSupNorm z' / 3 ^ n)| := h1
    _ ≤ _ := max_le h0 (h2.trans (max_le h0 le_rfl))

/-- The discrete curl of a function `ψ` in the plane of the coordinates `k, l`: the flow through
the lattice edge `(x, x + e_i)`. -/
noncomputable def planeCurlField (ψ : Vertex d → ℝ) (k l : Fin d) (x : Vertex d) (i : Fin d) :
    ℝ :=
  if i = k then ψ x - ψ (x - unit l) else if i = l then ψ (x - unit k) - ψ x else 0

/-- **Plane curls are divergence free.** -/
theorem sum_planeCurlField_sub_eq_zero (ψ : Vertex d → ℝ) {k l : Fin d} (hkl : k ≠ l)
    (x : Vertex d) :
    ∑ i : Fin d, (planeCurlField ψ k l x i - planeCurlField ψ k l (x - unit i) i) = 0 := by
  rw [Fintype.sum_eq_add k l hkl fun i hi => by
    simp only [planeCurlField, if_neg hi.1, if_neg hi.2, sub_self]]
  have e1 : ∀ y, planeCurlField ψ k l y k = ψ y - ψ (y - unit l) := fun y => if_pos rfl
  have e2 : ∀ y, planeCurlField ψ k l y l = ψ (y - unit k) - ψ y := fun y => by
    rw [planeCurlField, if_neg hkl.symm, if_pos rfl]
  rw [e1, e1, e2, e2, sub_right_comm x (unit k) (unit l)]
  ring

/-- The stream function `z_l χ_n(z)`. -/
noncomputable def cubeStream (n : ℕ) (l : Fin d) (z : Vertex d) : ℝ :=
  (z l : ℝ) * cubeCutoff n z

/-- **The solenoidal field** of scale `n` in the direction `e_k`, built in the plane of `k, l`. -/
noncomputable def cubeSolenoidalField (n : ℕ) (k l : Fin d) : Vertex d → Fin d → ℝ :=
  planeCurlField (cubeStream n l) k l

/-- **The solenoidal field is divergence free.** -/
theorem sum_cubeSolenoidalField_sub_eq_zero (n : ℕ) {k l : Fin d} (hkl : k ≠ l) (x : Vertex d) :
    ∑ i : Fin d, (cubeSolenoidalField n k l x i - cubeSolenoidalField n k l (x - unit i) i) = 0 :=
  sum_planeCurlField_sub_eq_zero _ hkl x

/-- **The solenoidal field equals `e_k` near `□_n`.** -/
theorem cubeSolenoidalField_eq_single {n : ℕ} {k l : Fin d} (hkl : k ≠ l) {x : Vertex d}
    (hx : vertexSupNorm x + 1 ≤ 3 ^ n) (i : Fin d) :
    cubeSolenoidalField n k l x i = (Pi.single k 1 : Fin d → ℝ) i := by
  have h1 : ∀ z, vertexSupNorm z ≤ 3 ^ n → cubeStream n l z = (z l : ℝ) := fun z hz => by
    rw [cubeStream, cubeCutoff_eq_one hz, mul_one]
  have hx0 := h1 x (by linarith [vertexSupNorm_nonneg x])
  have hxl := h1 (x - unit l) (by linarith [(vertexSupNorm_sub_unit_le x l).1])
  have hxk := h1 (x - unit k) (by linarith [(vertexSupNorm_sub_unit_le x k).1])
  have hsl : ((x - unit l) l : ℝ) = (x l : ℝ) - 1 := by
    change ((x l - (unit l : Vertex d) l : ℤ) : ℝ) = _
    rw [unit_apply_self]
    push_cast
    ring
  have hsk : ((x - unit k) l : ℝ) = (x l : ℝ) := by
    change ((x l - (unit k : Vertex d) l : ℤ) : ℝ) = _
    rw [unit_apply_ne hkl.symm, sub_zero]
  simp only [cubeSolenoidalField, planeCurlField]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, hx0, hxl, hsl, Pi.single_eq_same]
    ring
  · rw [if_neg hik, Pi.single_eq_of_ne hik]
    split_ifs
    · rw [hxk, hx0, hsk, sub_self]
    · rfl

/-- **The solenoidal field vanishes far from `□_n`.** -/
theorem cubeSolenoidalField_eq_zero {n : ℕ} (k l : Fin d) {x : Vertex d}
    (hx : 5 / 4 * 3 ^ n + 1 ≤ vertexSupNorm x) (i : Fin d) : cubeSolenoidalField n k l x i = 0 := by
  have hz : ∀ j : Fin d, cubeStream n l (x - unit j) = 0 := fun j => by
    rw [cubeStream, cubeCutoff_eq_zero (by linarith [(vertexSupNorm_sub_unit_le x j).2]),
      mul_zero]
  have hx0 : cubeStream n l x = 0 := by
    rw [cubeStream, cubeCutoff_eq_zero (by linarith), mul_zero]
  simp only [cubeSolenoidalField, planeCurlField]
  split_ifs <;> simp [hz, hx0]

/-- One increment of the stream function across an edge is at most `10`. -/
theorem abs_cubeStream_sub_le (n : ℕ) (l : Fin d) (z : Vertex d) (j : Fin d) :
    |cubeStream n l z - cubeStream n l (z - unit j)| ≤ 10 := by
  set z' := z - unit j with hz'
  have hfz : ∀ w : Vertex d, |(w l : ℝ)| ≤ vertexSupNorm w := fun w => abs_le_vertexSupNorm w l
  have hdiff : |(z l : ℝ) - (z' l : ℝ)| ≤ 1 := by
    have : ((z' l : ℤ) : ℝ) = (z l : ℝ) - ((unit j : Vertex d) l : ℝ) := by
      rw [hz']
      change (((z l - (unit j : Vertex d) l) : ℤ) : ℝ) = _
      push_cast
      ring
    rw [this]
    by_cases hj : l = j
    · subst hj
      rw [unit_apply_self]
      norm_num
    · rw [unit_apply_ne hj]
      norm_num
  have hχ := abs_cubeCutoff_sub_le n z z'
  have hsd : |vertexSupNorm z - vertexSupNorm z'| ≤ 1 := abs_vertexSupNorm_sub_unit_sub_le z j
  have hs := vertexSupNorm_sub_unit_le z j
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h31 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hχ' : |cubeCutoff n z - cubeCutoff n z'| ≤ 4 / 3 ^ n :=
    hχ.trans (div_le_div_of_nonneg_right (by linarith) h3.le)
  have hz1 := cubeCutoff_le_one n z
  have hz0 := cubeCutoff_nonneg n z
  have hsecond : |(z' l : ℝ)| * |cubeCutoff n z - cubeCutoff n z'| ≤ 9 := by
    by_cases hfar : 5 / 4 * 3 ^ n + 1 ≤ vertexSupNorm z'
    · rw [cubeCutoff_eq_zero (by linarith : 5 / 4 * 3 ^ n ≤ vertexSupNorm z),
        cubeCutoff_eq_zero (by linarith : 5 / 4 * 3 ^ n ≤ vertexSupNorm z'), sub_self, abs_zero,
        mul_zero]
      norm_num
    · replace hfar := not_le.1 hfar
      have hf' : |(z' l : ℝ)| ≤ 5 / 4 * 3 ^ n + 1 := (hfz z').trans hfar.le
      calc |(z' l : ℝ)| * |cubeCutoff n z - cubeCutoff n z'|
          ≤ (5 / 4 * 3 ^ n + 1) * (4 / 3 ^ n) :=
            mul_le_mul hf' hχ' (abs_nonneg _) (by positivity)
        _ = 5 + 4 / 3 ^ n := by field_simp
        _ ≤ 9 := by
            have : 4 / (3 : ℝ) ^ n ≤ 4 := div_le_self (by norm_num) h31
            linarith
  have e1 : cubeStream n l z - cubeStream n l z' =
      ((z l : ℝ) - (z' l : ℝ)) * cubeCutoff n z +
        (z' l : ℝ) * (cubeCutoff n z - cubeCutoff n z') := by
    simp only [cubeStream]
    ring
  rw [e1]
  calc _ ≤ |((z l : ℝ) - (z' l : ℝ)) * cubeCutoff n z| +
        |(z' l : ℝ) * (cubeCutoff n z - cubeCutoff n z')| := abs_add_le _ _
    _ = |(z l : ℝ) - (z' l : ℝ)| * cubeCutoff n z +
        |(z' l : ℝ)| * |cubeCutoff n z - cubeCutoff n z'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hz0]
    _ ≤ 1 * 1 + 9 := by
        gcongr
    _ = 10 := by norm_num

/-- **The solenoidal field is bounded** by `10`. -/
theorem abs_cubeSolenoidalField_le (n : ℕ) (k l : Fin d) (x : Vertex d) (i : Fin d) :
    |cubeSolenoidalField n k l x i| ≤ 10 := by
  simp only [cubeSolenoidalField, planeCurlField]
  split_ifs
  · exact abs_cubeStream_sub_le n l x l
  · rw [abs_sub_comm]
    exact abs_cubeStream_sub_le n l x k
  · norm_num

/-- **Summation by parts against a divergence-free field**: if the field vanishes off the edges
inside a finite set `T`, its pairing with every gradient over `T` vanishes. -/
theorem sum_mul_grad_eq_zero_of_div {F : Vertex d → Fin d → ℝ} (T : Finset (Vertex d))
    (hT : ∀ x i, F x i ≠ 0 → x ∈ T ∧ x + unit i ∈ T)
    (hdiv : ∀ x, ∑ i : Fin d, (F x i - F (x - unit i) i) = 0) (w : Vertex d → ℝ) :
    ∑ x ∈ T, ∑ i : Fin d, F x i * (w (x + unit i) - w x) = 0 := by
  have hshift : ∀ i : Fin d, ∑ x ∈ T, F x i * w (x + unit i) =
      ∑ y ∈ T, F (y - unit i) i * w y := by
    intro i
    refine Finset.sum_bij_ne_zero (fun x _ _ => x + unit i) (fun x _ hx => ?_)
      (fun x _ _ y _ _ h => add_right_cancel h) (fun y _ hy => ?_) (fun x _ _ => ?_)
    · exact (hT x i (left_ne_zero_of_mul hx)).2
    · refine ⟨y - unit i, (hT _ i (left_ne_zero_of_mul hy)).1, ?_, sub_add_cancel y _⟩
      rw [sub_add_cancel]
      exact hy
    · rw [add_sub_cancel_right]
  have e1 : ∑ x ∈ T, ∑ i : Fin d, F x i * (w (x + unit i) - w x) =
      ∑ i : Fin d, ∑ x ∈ T, F x i * w (x + unit i) -
        ∑ i : Fin d, ∑ x ∈ T, F x i * w x := by
    rw [← Finset.sum_sub_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [e1]
  simp only [hshift]
  have e3 : ∑ i : Fin d, ∑ y ∈ T, F (y - unit i) i * w y - ∑ i : Fin d, ∑ x ∈ T, F x i * w x =
      ∑ y ∈ T, ∑ i : Fin d, (F (y - unit i) i * w y - F y i * w y) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_sub_distrib]
  rw [e3]
  refine Finset.sum_eq_zero fun y _ => ?_
  have h := hdiv y
  have e2 : ∑ i : Fin d, (F (y - unit i) i * w y - F y i * w y) =
      -(w y * ∑ i : Fin d, (F y i - F (y - unit i) i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e2, h, mul_zero, neg_zero]

/-- The vertices of the triadic cube of scale `m` centred at the origin. -/
theorem mem_originCube_vertices_iff {m : ℕ} {x : Vertex d} :
    x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices ↔ ∀ i, |2 * x i| < 3 ^ m := by
  rw [TriadicCube.mem_toIntegerCube_vertices]
  change (∀ i, |2 * (x i - (3 : ℤ) ^ m * 0)| < 3 ^ m) ↔ _
  simp

/-- The solenoidal field of scale `n ≥ 2` vanishes on the lattice edges which are not edges of
`□_{n+1}`. -/
theorem cubeSolenoidalField_eq_zero_of_edge_not_mem {n : ℕ} (hn : 2 ≤ n) (k l : Fin d)
    {x : Vertex d} {i : Fin d}
    (h : ¬ (x ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices ∧
      x + unit i ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices)) :
    cubeSolenoidalField n k l x i = 0 := by
  apply cubeSolenoidalField_eq_zero
  by_contra hlt
  push Not at hlt
  have h9 : (9 : ℤ) ≤ 3 ^ n := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hb : ∀ j, 4 * |x j| < 5 * 3 ^ n + 4 := by
    intro j
    have h1 := abs_le_vertexSupNorm x j
    have h2 : (4 * |x j| : ℝ) < 5 * 3 ^ n + 4 := by
      have : ((|x j| : ℤ) : ℝ) = |(x j : ℝ)| := Int.cast_abs
      rw [← this] at h1
      linarith
    exact_mod_cast h2
  apply h
  rw [mem_originCube_vertices_iff, mem_originCube_vertices_iff]
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := hb j
    rw [abs_mul, abs_two, pow_succ]
    omega
  · have := hb j
    have hu : |(unit i : Vertex d) j| ≤ 1 := by
      by_cases hj : j = i
      · subst hj
        rw [unit_apply_self]
        norm_num
      · rw [unit_apply_ne hj]
        norm_num
    have ht := abs_add_le (x j) ((unit i : Vertex d) j)
    change |2 * (x j + (unit i : Vertex d) j)| < 3 ^ (n + 1)
    rw [abs_mul, abs_two, pow_succ]
    omega

/-- **Gradients are orthogonal to the solenoidal field** (Armstrong and Dario, display (5.28) with
right side `0`): its pairing with the gradient of any function over the edges of `□_{n+1}`
vanishes. -/
theorem latticeEdgePairing_cubeSolenoidalField_eq_zero {n : ℕ} (hn : 2 ≤ n) {k l : Fin d}
    (hkl : k ≠ l) (f : Vertex d → ℝ) :
    latticeEdgePairing (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices
      (cubeSolenoidalField n k l) f = 0 := by
  set W := (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices with hW
  have h := sum_mul_grad_eq_zero_of_div (F := cubeSolenoidalField n k l) W
    (fun x i hx => by
      by_contra hc
      exact hx (cubeSolenoidalField_eq_zero_of_edge_not_mem hn k l hc))
    (sum_cubeSolenoidalField_sub_eq_zero n hkl) f
  rw [latticeEdgePairing]
  refine (Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_).trans h
  split_ifs with hi
  · rfl
  · rw [cubeSolenoidalField_eq_zero_of_edge_not_mem hn k l (fun h => hi h.2), zero_mul]

/-- On `□_n` the solenoidal field is `e_k`, so its pairing over the edges of `□_n` is the pairing
of the constant field `e_k`. -/
theorem latticeEdgePairing_cubeSolenoidalField_origin (n : ℕ) {k l : Fin d} (hkl : k ≠ l)
    (f : Vertex d → ℝ) :
    latticeEdgePairing (⟨n, 0⟩ : TriadicCube d).toIntegerCube.vertices
      (cubeSolenoidalField n k l) f =
      latticeEdgePairing (⟨n, 0⟩ : TriadicCube d).toIntegerCube.vertices
        (fun _ => (Pi.single k 1 : Fin d → ℝ)) f := by
  unfold latticeEdgePairing
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · congr 1
    refine cubeSolenoidalField_eq_single hkl ?_ i
    rw [mem_originCube_vertices_iff] at hx
    have hb : ∀ j, (x j).natAbs + 1 ≤ 3 ^ n := by
      intro j
      have h := hx j
      rw [abs_mul, abs_two] at h
      have h1 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      have h2 : |x j| + 1 ≤ 3 ^ n := by omega
      have h3 : (((x j).natAbs + 1 : ℕ) : ℤ) ≤ ((3 ^ n : ℕ) : ℤ) := by
        push_cast
        exact h2
      exact_mod_cast h3
    have hs : vertexSupNorm x ≤ ((3 ^ n - 1 : ℕ) : ℝ) :=
      vertexSupNorm_le_iff.2 fun j => by have := hb j; omega
    have h1 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have : ((3 ^ n - 1 : ℕ) : ℝ) = (3 : ℝ) ^ n - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    linarith
  · rfl

end Rigidity.Percolation
