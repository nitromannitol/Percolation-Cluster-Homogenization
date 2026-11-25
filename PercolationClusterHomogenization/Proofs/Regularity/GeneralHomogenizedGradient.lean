import PercolationClusterHomogenization.Proofs.Regularity.PlanarHomogenizedGradient

/-!
# Interior gradient bound for the discrete homogenized solution in every dimension

For `v` harmonic for the lattice Laplacian on the interior of the lattice cube `□_n` of `ℤᵈ`,
`T ≥ 1` and a point `x` at distance at least `d (T + 2) + T + 2` from the boundary of `□_n`,
`|v(x + e_l) - v(x)| ≤ 2^d (10 d)^{d/2} T^{-d/2} (Σ_{edges in □_n} |∇v|²)^{1/2}`
(`abs_grad_le_of_cubeInterior_cube`): the difference `∇_l v` is harmonic one slice further in, and
the interior `L^∞` bound for constant-coefficient harmonic functions
(`abs_le_of_condLaplacian_constCond_eq_zero`) with `M = r = T` bounds it by its `L²` norm. Along a
staircase path, the increments give `|v(z) - v(y)| ≤ |z - y|₁ G`
(`abs_sub_le_of_grad_le_cube`). The planar forms are `abs_grad_le_of_cubeInterior` and
`abs_sub_le_of_grad_le`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Dirichlet

variable {d : ℕ}

theorem two_mul_toIntegerCube_corner_add_cube (n : ℕ) (k : Fin d) :
    2 * (⟨n, 0⟩ : TriadicCube d).toIntegerCube.corner k + 3 ^ n = 1 := by
  have ho : (3 : ℤ) ^ n % 2 = 1 := Int.odd_iff.mp (Odd.pow ⟨1, by norm_num⟩)
  have hd := Int.emod_add_mul_ediv ((3 : ℤ) ^ n) 2
  change 2 * ((3 : ℤ) ^ n * (0 : Vertex d) k - (3 : ℤ) ^ n / 2) + 3 ^ n = 1
  rw [Pi.zero_apply, mul_zero, zero_sub]
  omega

theorem cast_toIntegerCube_size_zero_cube (n : ℕ) :
    (((⟨n, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℤ) = 3 ^ n := by
  change ((3 ^ n : ℕ) : ℤ) = _
  push_cast
  rfl

theorem unit_apply_cube (l k : Fin d) : (unit l : Vertex d) k = if k = l then 1 else 0 := by
  simp only [unit, Pi.single_apply]

/-- One term of the interior `L^∞` bound with `M = r = T`. -/
theorem interior_term_le {T : ℕ} (hT : 0 < T) (E : ℝ) {c : ℕ} (hc : c ≤ d)
    (hd : 0 < d) :
    (1 / (T : ℝ)) ^ (d - c) * (√((T : ℝ) ^ d) *
        √((10 * (d : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ c * E)) ≤
      √((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d) * √E := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd1 : (1 : ℝ) ≤ 10 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hTd : (0 : ℝ) < (T : ℝ) ^ d := by positivity
  have hsT : 0 < √((T : ℝ) ^ d) := Real.sqrt_pos.2 hTd
  have e1 : (10 * (d : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ c = (10 * d) ^ c / ((T : ℝ) ^ c) ^ 2 := by
    rw [div_pow, mul_one, one_mul, ← pow_mul, ← pow_mul, mul_comm 2 c]
  have e2 : √((10 * (d : ℝ)) ^ c / ((T : ℝ) ^ c) ^ 2 * E) =
      √((10 * (d : ℝ)) ^ c) / (T : ℝ) ^ c * √E := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [e1, e2]
  have hTdc : (T : ℝ) ^ d = (T : ℝ) ^ (d - c) * (T : ℝ) ^ c := by
    rw [← pow_add]; congr 1; omega
  have hmono : √((10 * (d : ℝ)) ^ c) ≤ √((10 * (d : ℝ)) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hd1 hc)
  have hsE := Real.sqrt_nonneg E
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √((T : ℝ) ^ d) := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 < s := by rw [hs]; exact hsT
  have hsne : s ≠ 0 := hs0.ne'
  have hs2 : s * s = (T : ℝ) ^ d := by rw [hs]; exact Real.mul_self_sqrt hTd.le
  have hTne : (T : ℝ) ≠ 0 := hT0.ne'
  calc (1 / (T : ℝ)) ^ (d - c) * (s * (√((10 * (d : ℝ)) ^ c) / (T : ℝ) ^ c * √E))
      = √((10 * (d : ℝ)) ^ c) * √E * s / ((T : ℝ) ^ (d - c) * (T : ℝ) ^ c) := by
        rw [one_div_pow]; field_simp
    _ = √((10 * (d : ℝ)) ^ c) * √E * s / (T : ℝ) ^ d := by rw [hTdc]
    _ = √((10 * (d : ℝ)) ^ c) * √E / s := by rw [← hs2]; field_simp
    _ ≤ √((10 * (d : ℝ)) ^ d) * √E / s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hsE) hs0.le
    _ = √((10 * (d : ℝ)) ^ d) / s * √E := by ring

set_option maxHeartbeats 400000 in
/-- **Interior gradient bound** in dimension `d`: for `v` harmonic for the lattice Laplacian on the
interior of the lattice cube `□_n`, `T ≥ 1`, and `x` with
`2 |x_k| + 2 d (T + 2) + 2 T + 3 ≤ 3^n` for every `k`,
`|v(x + e_l) - v(x)| ≤ 2^d (10 d)^{d/2} T^{-d/2} (Σ_{edges in □_n} |∇v|²)^{1/2}`. -/
theorem abs_grad_le_of_cubeInterior_cube (hd : 0 < d) {n T : ℕ} (hT : 0 < T)
    {v : Vertex d → ℝ}
    (hv : ∀ x ∈ cubeInterior (⟨n, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) v x = 0)
    {x : Vertex d}
    (hx : ∀ k, 2 * |x k| + 2 * (((d * (T + 2) : ℕ) : ℤ)) + 2 * (T : ℤ) + 3 ≤ 3 ^ n)
    (l : Fin d) :
    |v (x + unit l) - v x| ≤ 2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨n, 0⟩ : TriadicCube d).toIntegerCube
        v) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : IntegerCube d, Q = (⟨n, 0⟩ : TriadicCube d).toIntegerCube :=
    ⟨_, rfl⟩
  rw [← hQ] at hv ⊢
  have hc : ∀ k, 2 * Q.corner k + 3 ^ n = 1 := fun k => by
    rw [hQ]; exact two_mul_toIntegerCube_corner_add_cube _ k
  have hs : ((Q.size : ℕ) : ℤ) = 3 ^ n := by rw [hQ]; exact cast_toIntegerCube_size_zero_cube _
  -- the difference is harmonic one slice further in
  have hh : ∀ y ∈ (shrinkCube (shrinkCube Q 1) 1).vertices,
      condLaplacian (constCond fun _ => (1 : ℝ)) (fun y => v (y + unit l) - v y) y = 0 := by
    intro y hy
    refine condLaplacian_constCond_grad_eq_zero (fun _ => (1 : ℝ)) hv l y ?_
    rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff] at hy
    have hmem : ∀ w : Vertex d, (∀ k, Q.corner k + 1 ≤ w k ∧ w k + 2 ≤ Q.corner k + Q.size) →
        w ∈ cubeInterior Q := by
      intro w hw
      unfold cubeInterior
      rw [Finset.mem_filter, IntegerCube.mem_vertices]
      refine ⟨fun k => ?_, hw⟩
      have := hw k
      constructor <;> omega
    rw [Finset.mem_filter]
    constructor
    · refine hmem y fun k => ?_
      have := hy k
      constructor <;> omega
    · refine hmem _ fun k => ?_
      have := hy k
      rw [Pi.add_apply, unit_apply_cube]
      split_ifs <;> constructor <;> omega
  -- the cube of side `T` at `x`
  have hxM : (cornerCube x T).vertices ⊆
      (shrinkCube (shrinkCube Q 1) (d * (T + 2))).vertices := by
    intro y hy
    rw [IntegerCube.mem_vertices] at hy
    rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff]
    intro k
    have h1 := hy k
    change x k ≤ y k ∧ y k < x k + ((T : ℕ) : ℤ) at h1
    have h2 := hx k
    have h3 := hc k
    have h4 := le_abs_self (x k)
    have h5 := neg_abs_le (x k)
    obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d * (T + 2) := ⟨_, rfl⟩
    rw [← hD] at h2 ⊢
    have hs' := hs
    generalize |x k| = a at h2 h4 h5
    generalize (3 : ℤ) ^ n = N at h2 h3 hs'
    constructor <;> omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hb := abs_le_of_condLaplacian_constCond_eq_zero (d := d) hd (fun _ => (1 : ℝ))
    (lam := 1) (Λ := 1) one_pos (fun _ => ⟨le_rfl, le_rfl⟩) (shrinkCube Q 1) hh
    (r := T) hT (M := T) hT hxM
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ y ∈ (shrinkCube Q 1).vertices, (v (y + unit l) - v y) ^ 2 :=
    ⟨_, rfl⟩
  rw [← hE] at hb
  have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      (1 / (T : ℝ)) ^ (d - S.card) * (√((T : ℝ) ^ d) *
        √((10 * (d : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ S.card * E)) ≤
        √((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d) * √E := by
    intro S _
    have hcard : S.card ≤ d := by simpa using Finset.card_le_univ S
    exact interior_term_le hT E hcard hd
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin d)).powerset
    (fun S => (1 / (T : ℝ)) ^ (d - S.card) * (√((T : ℝ) ^ d) *
      √((10 * (d : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ S.card * E)))
    (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d) * √E) hterm
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hEI : E ≤ innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q v := by
    rw [hE]
    unfold innerEdgeEnergy
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ x ∈ Q.vertices.filter
      (fun x => x + unit j ∈ Q.vertices), constCond (fun _ => (1 : ℝ)) (x, j) *
        (v (x + unit j) - v x) ^ 2) (fun j _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (by simp [constCond]) (sq_nonneg _)) (Finset.mem_univ l))
    refine le_of_le_of_eq (b := ∑ y ∈ Q.vertices.filter (fun x => x + unit l ∈ Q.vertices),
      (v (y + unit l) - v y) ^ 2)
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _) ?_
    · intro y hy
      rw [mem_shrinkCube_iff] at hy
      rw [Finset.mem_filter, IntegerCube.mem_vertices, IntegerCube.mem_vertices]
      refine ⟨fun k => ?_, fun k => ?_⟩
      · have := hy k; constructor <;> omega
      · have := hy k
        rw [Pi.add_apply, unit_apply_cube]
        split_ifs <;> constructor <;> omega
    · refine Finset.sum_congr rfl fun y _ => ?_
      simp [constCond]
  calc |v (x + unit l) - v x| ≤ _ := hb
    _ ≤ ((2 ^ d : ℕ) : ℝ) * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d) * √E) := hsum
    _ = 2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) * √E := by push_cast; ring
    _ ≤ 2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) *
          √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q v) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEI) (by positivity)

/-- The point that agrees with `z` on the coordinates below `k` and with `y` on the others. -/
def stairPoint (y z : Vertex d) (k : ℕ) : Vertex d := fun i => if (i : ℕ) < k then z i else y i

theorem stairPoint_zero (y z : Vertex d) : stairPoint y z 0 = y := by
  funext i; simp [stairPoint]

theorem stairPoint_of_le (y z : Vertex d) {k : ℕ} (hk : d ≤ k) : stairPoint y z k = z := by
  funext i
  have : (i : ℕ) < k := lt_of_lt_of_le i.isLt hk
  simp [stairPoint, this]

set_option maxHeartbeats 400000 in
/-- **Increments along a staircase** in dimension `d`: if the unit increments of `v` on the box
spanned by `y` and `z` are at most `G`, then `|v(z) - v(y)| ≤ |z - y|₁ G`. -/
theorem abs_sub_le_of_grad_le_cube (v : Vertex d → ℝ) {G : ℝ} (y z : Vertex d)
    (h : ∀ p : Vertex d, (∀ k, min (y k) (z k) ≤ p k ∧ p k ≤ max (y k) (z k)) →
      ∀ l, |v (p + unit l) - v p| ≤ G) :
    |v z - v y| ≤ ((∑ k, |z k - y k| : ℤ) : ℝ) * G := by
  have hstep : ∀ k : ℕ, |v (stairPoint y z k) - v y| ≤
      ((∑ i : Fin d, if (i : ℕ) < k then |z i - y i| else 0 : ℤ) : ℝ) * G := by
    intro k
    induction k with
    | zero =>
        rw [stairPoint_zero]
        simp
    | succ k ih =>
        by_cases hk : k < d
        · obtain ⟨i₀, hi₀⟩ : ∃ i : Fin d, i = ⟨k, hk⟩ := ⟨_, rfl⟩
          have hseg := abs_sub_le_of_abs_succ_sub_le
            (fun t => v (Function.update (stairPoint y z k) i₀ t)) (y i₀) (z i₀)
            fun t ht1 ht2 => by
              have hbox : ∀ j, min (y j) (z j) ≤ Function.update (stairPoint y z k) i₀ t j ∧
                  Function.update (stairPoint y z k) i₀ t j ≤ max (y j) (z j) := by
                intro j
                by_cases hj : j = i₀
                · rw [hj, Function.update_self]
                  exact ⟨ht1, by omega⟩
                · rw [Function.update_of_ne hj]
                  simp only [stairPoint]
                  split_ifs
                  · exact ⟨min_le_right _ _, le_max_right _ _⟩
                  · exact ⟨min_le_left _ _, le_max_left _ _⟩
              have hp := h _ hbox i₀
              have e : Function.update (stairPoint y z k) i₀ t + unit i₀ =
                  Function.update (stairPoint y z k) i₀ (t + 1) := by
                funext j
                by_cases hj : j = i₀
                · rw [hj]; simp [unit_apply_cube]
                · simp [unit_apply_cube, hj]
              rw [e] at hp
              exact hp
          have e1 : Function.update (stairPoint y z k) i₀ (y i₀) = stairPoint y z k := by
            funext j
            by_cases hj : j = i₀
            · rw [hj]; simp [stairPoint, hi₀]
            · rw [Function.update_of_ne hj]
          have e2 : Function.update (stairPoint y z k) i₀ (z i₀) = stairPoint y z (k + 1) := by
            funext j
            by_cases hj : j = i₀
            · rw [hj]; simp [stairPoint, hi₀]
            · rw [Function.update_of_ne hj]
              simp only [stairPoint]
              have hjk : (j : ℕ) ≠ k := fun h' => hj (Fin.ext (by rw [hi₀]; exact h'))
              by_cases hjl : (j : ℕ) < k
              · simp [hjl, show (j : ℕ) < k + 1 by omega]
              · simp [hjl, show ¬ (j : ℕ) < k + 1 by omega]
          simp only [e1, e2] at hseg
          have hsum : (∑ i : Fin d, if (i : ℕ) < k + 1 then |z i - y i| else 0 : ℤ) =
              (∑ i : Fin d, if (i : ℕ) < k then |z i - y i| else 0) + |z i₀ - y i₀| := by
            have hsplit : ∀ i : Fin d, (if (i : ℕ) < k + 1 then |z i - y i| else 0) =
                (if (i : ℕ) < k then |z i - y i| else 0) + (if i = i₀ then |z i - y i| else 0) := by
              intro i
              by_cases hik : (i : ℕ) < k
              · have hne : i ≠ i₀ := fun h' => by rw [h', hi₀] at hik; exact lt_irrefl _ hik
                simp [hik, show (i : ℕ) < k + 1 by omega, hne]
              · by_cases hie : i = i₀
                · rw [hie]; simp [hi₀]
                · have hik' : ¬ (i : ℕ) < k + 1 := by
                    intro h'
                    have : (i : ℕ) = k := by omega
                    exact hie (Fin.ext (by rw [hi₀]; exact this))
                  simp [hik, hik', hie]
            rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
              Finset.sum_ite_eq' Finset.univ i₀, if_pos (Finset.mem_univ _)]
          calc |v (stairPoint y z (k + 1)) - v y|
              ≤ |v (stairPoint y z (k + 1)) - v (stairPoint y z k)| +
                  |v (stairPoint y z k) - v y| := abs_sub_le _ _ _
            _ ≤ ((|z i₀ - y i₀| : ℤ) : ℝ) * G +
                  ((∑ i : Fin d, if (i : ℕ) < k then |z i - y i| else 0 : ℤ) : ℝ) * G :=
                add_le_add hseg ih
            _ = _ := by rw [hsum]; push_cast; ring
        · have e : stairPoint y z (k + 1) = stairPoint y z k := by
            rw [stairPoint_of_le y z (show d ≤ k + 1 by omega),
              stairPoint_of_le y z (show d ≤ k by omega)]
          have hs : (∑ i : Fin d, if (i : ℕ) < k + 1 then |z i - y i| else 0 : ℤ) =
              ∑ i : Fin d, if (i : ℕ) < k then |z i - y i| else 0 :=
            Finset.sum_congr rfl fun i _ => by
              have h1 : (i : ℕ) < k := lt_of_lt_of_le i.isLt (by omega)
              simp [h1, show (i : ℕ) < k + 1 by omega]
          rw [e, hs]
          exact ih
  have h := hstep d
  rw [stairPoint_of_le y z le_rfl] at h
  have hs : (∑ i : Fin d, if (i : ℕ) < d then |z i - y i| else 0 : ℤ) = ∑ k, |z k - y k| :=
    Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  rwa [hs] at h

end Rigidity.Proofs.Regularity
