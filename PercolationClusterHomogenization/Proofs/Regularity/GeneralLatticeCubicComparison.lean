import PercolationClusterHomogenization.Proofs.Regularity.GeneralLatticeExcessThree

/-!
# Lattice harmonic cubic polynomials over quadratic functions on the balls of `ℤᵈ`

The excess over `Ā_2` of an element `w = q + cubicForm t (·) / 6` of `Ā_3` on the ball `B_ρ(z)` is
at most `(∑ |tᵢⱼₖ|) ρ³ / 6`: the recentred cubic part `tensorCubicPart t z` is the difference of
`w` and a lattice harmonic quadratic function (`ballExcess_cubicPoly_le`). Conversely, for every
quadratic function `h` the third forward differences of `w - h` are the entries of `t`, so its
mixed third difference with step `n` in the directions `eₐ, e_b, e_e` is `n³ tₐ_b_e`
(`stepFwd_stepFwd_stepFwd_eq`); this difference is a signed sum of eight values of `w - h`, and
summing its square over a box of side `n ≈ ρ / (4 √d)` bounds `|tₐ_b_e| ρ³` by a constant times
the normalized norm of `w - h` on `B_ρ(z)` (`le_componentBallL2_of_fwd3`). This gives
`PolynomialComparison` for `Ā_2 ≤ Ā_3` with degree `3` on the balls of `ℤᵈ`
(`polynomialComparison_latticeHarmonicCubicPoly`), the comparison
`polynomialComparison_latticeHarmonicCubic` of the plane in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-! ### Differences with a step -/

/-- The forward difference `h(y + n eᵢ) - h(y)` with step `n`. -/
def stepFwd (i : Fin d) (n : ℤ) (h : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : ℝ :=
  h (y + n • unit i) - h y

theorem stepFwd_eq_sum (i : Fin d) (n : ℕ) (h : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) :
    stepFwd i n h y = ∑ k ∈ range n, fwd i h (y + (k : ℤ) • unit i) := by
  induction n with
  | zero => simp [stepFwd]
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    simp only [stepFwd, fwd]
    push_cast
    rw [add_smul, one_smul, ← add_assoc]
    ring

theorem fwd_stepFwd_comm (a b : Fin d) (n : ℤ) (h : (Fin d → ℤ) → ℝ) :
    fwd a (stepFwd b n h) = stepFwd b n (fwd a h) := by
  funext y
  simp only [fwd, stepFwd]
  rw [add_right_comm y (unit a) (n • unit b)]
  ring

theorem stepFwd_eq_of_fwd_eq {i : Fin d} (n : ℕ) {h : (Fin d → ℤ) → ℝ} {c : ℝ}
    (hc : ∀ y, fwd i h y = c) (y : Fin d → ℤ) : stepFwd i n h y = n * c := by
  rw [stepFwd_eq_sum]
  simp [hc]

theorem stepFwd_stepFwd_eq {a b : Fin d} (n : ℕ) {h : (Fin d → ℤ) → ℝ} {c : ℝ}
    (hc : ∀ y, fwd b (fwd a h) y = c) (y : Fin d → ℤ) :
    stepFwd b n (stepFwd a n h) y = n * (n * c) := by
  apply stepFwd_eq_of_fwd_eq
  intro y'
  rw [fwd_stepFwd_comm]
  apply stepFwd_eq_of_fwd_eq
  intro y''
  rw [fwd_comm]
  exact hc y''

/-- **Mixed third differences with a step** of a function with constant third differences. -/
theorem stepFwd_stepFwd_stepFwd_eq {a b e : Fin d} (n : ℕ) {h : (Fin d → ℤ) → ℝ} {γ : ℝ}
    (hγ : ∀ y, fwd e (fwd b (fwd a h)) y = γ) (y : Fin d → ℤ) :
    stepFwd e n (stepFwd b n (stepFwd a n h)) y = n * (n * (n * γ)) := by
  apply stepFwd_eq_of_fwd_eq
  intro y'
  rw [fwd_stepFwd_comm, fwd_stepFwd_comm]
  apply stepFwd_stepFwd_eq
  intro y''
  rw [fwd_comm a e, fwd_comm b e]
  exact hγ y''

theorem sq_add_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

theorem sq_add8_le (a b c d e f g h : ℝ) :
    (a + b + c + d + e + f + g + h) ^ 2 ≤
      8 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2) := by
  have h4 : ∀ p q r s : ℝ, (p + q + r + s) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) := by
    intro p q r s
    have h1 := sq_add_le_two_mul (p + q) (r + s)
    have h2 := sq_add_le_two_mul p q
    have h3 := sq_add_le_two_mul r s
    have e : p + q + r + s = (p + q) + (r + s) := by ring
    rw [e]
    linarith
  have h1 := sq_add_le_two_mul (a + b + c + d) (e + f + g + h)
  have h2 := h4 a b c d
  have h3 := h4 e f g h
  have e1 : a + b + c + d + e + f + g + h = (a + b + c + d) + (e + f + g + h) := by ring
  rw [e1]
  linarith

theorem smul_unit_apply_bounds (n : ℕ) (i j : Fin d) :
    0 ≤ ((n : ℤ) • unit i) j ∧ ((n : ℤ) • unit i) j ≤ n := by
  simp only [Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
  split_ifs <;> constructor <;> omega

/-- The constant of the lower bound by mixed third differences. -/
noncomputable def mixedThirdConst (d : ℕ) : ℝ :=
  8 * Real.sqrt (3 ^ d * (8 * Real.sqrt d) ^ (d + 6))

theorem mixedThirdConst_pos (hd : 0 < d) : 0 < mixedThirdConst d := by
  have h : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  unfold mixedThirdConst
  exact mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos (by positivity)
    (pow_pos (mul_pos (by norm_num) h) _)))

/-- **Lower bound by a mixed third difference.** If the third forward differences
`D_e D_b D_a G` are equal to `γ` everywhere, then `|γ| ρ³ ≤ mixedThirdConst d ‖G‖_{L̲²(B_ρ(z))}`
on the balls of `ℤᵈ` with `ρ ≥ 8 √d`. -/
theorem le_componentBallL2_of_fwd3 [NeZero d] (z : Vertex d) {ρ : ℝ}
    (hρ : 8 * Real.sqrt d ≤ ρ) (G : (Fin d → ℤ) → ℝ) (a b e : Fin d) (γ : ℝ)
    (hG : ∀ y, fwd e (fwd b (fwd a G)) y = γ) :
    |γ| * ρ ^ 3 ≤ mixedThirdConst d * componentBallL2 (latticeComponent d) z ρ
      (fun x => G x.val) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hsd : 0 < Real.sqrt d := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hρ8 : 8 ≤ ρ := by linarith
  set n := ⌊ρ / (4 * Real.sqrt d)⌋₊ with hn
  have hnle : (n : ℝ) ≤ ρ / (4 * Real.sqrt d) := Nat.floor_le (by positivity)
  have hnge : ρ / (8 * Real.sqrt d) ≤ n := by
    have h1 := Nat.lt_floor_add_one (ρ / (4 * Real.sqrt d))
    rw [← hn] at h1
    have h2 : 1 ≤ ρ / (8 * Real.sqrt d) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : ρ / (4 * Real.sqrt d) = 2 * (ρ / (8 * Real.sqrt d)) := by field_simp; ring
    linarith
  set box := latticeBox univ (z - fun _ => (n : ℤ)) n with hbox
  have hshift : ∀ y ∈ box, ∀ v : Fin d → ℤ, (∀ j, 0 ≤ v j ∧ v j ≤ 3 * n) →
      y + v ∈ supBox z (3 * n) := by
    intro y hy v hv
    simp only [hbox, latticeBox, Fintype.mem_piFinset, mem_univ, if_true, mem_Icc] at hy
    simp only [supBox, Fintype.mem_piFinset, mem_Icc]
    intro j
    have h1 := hy j
    have h2 := hv j
    simp only [Pi.sub_apply, Pi.add_apply] at h1 ⊢
    push_cast
    constructor <;> omega
  have hu := smul_unit_apply_bounds (d := d) n
  set S := ∑ y ∈ supBox z (3 * n), G y ^ 2 with hS
  have hk : ∀ v : Fin d → ℤ, (∀ j, 0 ≤ v j ∧ v j ≤ 3 * n) →
      ∑ y ∈ box, G (y + v) ^ 2 ≤ S := fun v hv =>
    sum_comp_add_le (fun y => G y ^ 2) (fun _ => sq_nonneg _) v (fun y hy => hshift y hy v hv)
  -- the eight shifts
  obtain ⟨ua, hua⟩ : ∃ v : Fin d → ℤ, v = (n : ℤ) • unit a := ⟨_, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ v : Fin d → ℤ, v = (n : ℤ) • unit b := ⟨_, rfl⟩
  obtain ⟨ue, hue⟩ : ∃ v : Fin d → ℤ, v = (n : ℤ) • unit e := ⟨_, rfl⟩
  have hua' : ∀ j, 0 ≤ ua j ∧ ua j ≤ n := by rw [hua]; exact hu a
  have hub' : ∀ j, 0 ≤ ub j ∧ ub j ≤ n := by rw [hub]; exact hu b
  have hue' : ∀ j, 0 ≤ ue j ∧ ue j ≤ n := by rw [hue]; exact hu e
  have hv1 := hk (ue + (ub + ua)) fun j => by
    have := hue' j; have := hub' j; have := hua' j
    simp only [Pi.add_apply]; constructor <;> omega
  have hv2 := hk (ue + ub) fun j => by
    have := hue' j; have := hub' j
    simp only [Pi.add_apply]; constructor <;> omega
  have hv3 := hk (ue + ua) fun j => by
    have := hue' j; have := hua' j
    simp only [Pi.add_apply]; constructor <;> omega
  have hv4 := hk ue fun j => by have := hue' j; constructor <;> omega
  have hv5 := hk (ub + ua) fun j => by
    have := hub' j; have := hua' j
    simp only [Pi.add_apply]; constructor <;> omega
  have hv6 := hk ub fun j => by have := hub' j; constructor <;> omega
  have hv7 := hk ua fun j => by have := hua' j; constructor <;> omega
  have hv8 := hk 0 fun j => by simp
  simp only [add_zero] at hv8
  -- the pointwise inequality
  have hpt : ∀ y ∈ box, (n : ℝ) ^ 6 * γ ^ 2 ≤
      8 * (G (y + (ue + (ub + ua))) ^ 2 + G (y + (ue + ub)) ^ 2 + G (y + (ue + ua)) ^ 2 +
        G (y + ue) ^ 2 + G (y + (ub + ua)) ^ 2 + G (y + ub) ^ 2 + G (y + ua) ^ 2 + G y ^ 2) := by
    intro y _
    have h := stepFwd_stepFwd_stepFwd_eq n hG y
    simp only [stepFwd, add_assoc] at h
    rw [← hua, ← hub, ← hue] at h
    have key := sq_add8_le (G (y + (ue + (ub + ua)))) (-G (y + (ue + ub))) (-G (y + (ue + ua)))
      (G (y + ue)) (-G (y + (ub + ua))) (G (y + ub)) (G (y + ua)) (-G y)
    have e1 : G (y + (ue + (ub + ua))) + -G (y + (ue + ub)) + -G (y + (ue + ua)) + G (y + ue) +
        -G (y + (ub + ua)) + G (y + ub) + G (y + ua) + -G y = n * (n * (n * γ)) := by
      rw [← h]; ring
    rw [e1] at key
    simp only [neg_sq] at key
    calc (n : ℝ) ^ 6 * γ ^ 2 = (n * (n * (n * γ))) ^ 2 := by ring
      _ ≤ _ := key
  have hsum := sum_le_sum hpt
  rw [sum_const, card_latticeBox_univ, nsmul_eq_mul, ← mul_sum] at hsum
  simp only [sum_add_distrib] at hsum
  have hTS : ((n + 1 : ℕ) : ℝ) ^ d * ((n : ℝ) ^ 6 * γ ^ 2) ≤ 64 * S := by
    push_cast at hsum ⊢
    linarith
  -- the ball
  have hL : Real.sqrt d * ((3 * n : ℕ) : ℝ) < ρ := by
    have h3 : ((3 * n : ℕ) : ℝ) ≤ 3 * (ρ / (4 * Real.sqrt d)) := by push_cast; linarith
    have e : Real.sqrt d * (3 * (ρ / (4 * Real.sqrt d))) = 3 * ρ / 4 := by field_simp
    have := mul_le_mul_of_nonneg_left h3 hsd.le
    linarith
  have hball := sum_sq_supBox_le_ball z hL G
  set N := componentBallL2 (latticeComponent d) z ρ (fun x => G x.val) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  have hsq : ∑ x ∈ componentEuclideanBall (latticeComponent d) z ρ, G x.val ^ 2 =
      ((componentEuclideanBall (latticeComponent d) z ρ).card : ℝ) * N ^ 2 :=
    sum_sq_eq_card_mul_componentBallL2_sq (latticeComponent d) z ρ (fun x => G x.val)
  have hcard : ((componentEuclideanBall (latticeComponent d) z ρ).card : ℝ) ≤ (3 * ρ) ^ d :=
    (card_componentEuclideanBall_le (latticeComponent d) z hρ0.le).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) d)
  have hmain : ((n + 1 : ℕ) : ℝ) ^ d * ((n : ℝ) ^ 6 * γ ^ 2) ≤ 64 * ((3 * ρ) ^ d * N ^ 2) := by
    refine hTS.trans ?_
    rw [hS]
    refine mul_le_mul_of_nonneg_left (hball.trans ?_) (by norm_num)
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  -- the lower bound of the box
  set Q := ρ / (8 * Real.sqrt d) with hQ
  have hQ0 : 0 < Q := by positivity
  have hQn1 : Q ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hlow : Q ^ d * Q ^ 6 * γ ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ d * ((n : ℝ) ^ 6 * γ ^ 2) := by
    have h1 : Q ^ d ≤ ((n + 1 : ℕ) : ℝ) ^ d := pow_le_pow_left₀ hQ0.le hQn1 d
    have h2 : Q ^ 6 ≤ (n : ℝ) ^ 6 := pow_le_pow_left₀ hQ0.le hnge 6
    have := mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (sq_nonneg γ)) (by positivity)
      (by positivity)
    linarith
  have hQd : Q ^ d * Q ^ 6 = ρ ^ d * ρ ^ 6 / (8 * Real.sqrt d) ^ (d + 6) := by
    rw [hQ, div_pow, div_pow, pow_add]; field_simp
  have hfin : (ρ ^ 3 * |γ|) ^ 2 ≤ (mixedThirdConst d * N) ^ 2 := by
    have h1 := hlow.trans hmain
    rw [hQd] at h1
    have hK : 0 < (8 * Real.sqrt d) ^ (d + 6) := by positivity
    have hρd : 0 < ρ ^ d := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hK] at h1
    have e1 : (mixedThirdConst d * N) ^ 2 = 64 * (3 ^ d * (8 * Real.sqrt d) ^ (d + 6)) * N ^ 2 := by
      rw [mixedThirdConst, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [e1, mul_pow, sq_abs]
    have e2 : 64 * ((3 * ρ) ^ d * N ^ 2) * (8 * Real.sqrt d) ^ (d + 6) =
        ρ ^ d * (64 * (3 ^ d * (8 * Real.sqrt d) ^ (d + 6)) * N ^ 2) := by
      rw [mul_pow]; ring
    rw [e2] at h1
    have e3 : ρ ^ d * ρ ^ 6 * γ ^ 2 = ρ ^ d * ((ρ ^ 3) ^ 2 * γ ^ 2) := by ring
    rw [e3] at h1
    exact le_of_mul_le_mul_left h1 hρd
  have h0 : 0 ≤ mixedThirdConst d * N := mul_nonneg (mixedThirdConst_pos hd).le hN0
  have h3 : 0 ≤ ρ ^ 3 * |γ| := by positivity
  rw [mul_comm |γ|]
  exact (pow_le_pow_iff_left₀ h3 h0 two_ne_zero).1 hfin

/-- **Upper bound for the excess of a lattice harmonic cubic polynomial over `Ā_2`.** -/
theorem ballExcess_cubicPoly_le [NeZero d] (z : Vertex d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {w : latticeComponent d → ℝ} {t : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t)
    (htr : ∀ k, tensorTrace t k = 0)
    (hq : (fun x => w x - cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈
      latticeHarmonicQuadratic d) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicQuadratic d) ρ w ≤
      (∑ i, ∑ j, ∑ k, |t i j k|) * ρ ^ 3 / 6 := by
  have hmem := sub_tensorCubicPart_mem_latticeHarmonicQuadratic ht htr hq z
  refine (ballExcess_le _ _ hmem).trans ?_
  rw [componentBallSeminorm_apply]
  apply componentBallL2_le_of_abs_le _ _ _ (by positivity)
  intro x hx
  have e : (w - fun x => w x - tensorCubicPart t z x.val) x = tensorCubicPart t z x.val := by
    simp
  rw [e, tensorCubicPart, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply abs_cubicForm_le
  intro i
  rw [mem_componentEuclideanBall] at hx
  have e : (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) i =
      ((x.val i : ℝ) - z i) := by
    rw [← latticeEuclideanEmbedding_sub]
    change (((x.val - z) i : ℤ) : ℝ) = _
    push_cast [Pi.sub_apply]
    ring
  rw [e]
  exact (abs_sub_le_dist_latticeEuclideanEmbedding x.val z i).trans hx.le

/-- The constant of the comparison of `Ā_3` with `Ā_2`. -/
noncomputable def cubicCompConst (d : ℕ) : ℝ := d ^ 3 * mixedThirdConst d / 6

/-- **Polynomial comparison for the lattice harmonic cubic polynomials over `Ā_2` on the balls of
`ℤᵈ`**, with degree `3`, above the radius `8 √d`. -/
theorem polynomialComparison_latticeHarmonicCubicPoly [NeZero d] (z : Vertex d) (R : ℝ) :
    PolynomialComparison (componentBallSeminorm (latticeComponent d) z)
      (latticeHarmonicQuadratic d) (latticeHarmonicCubicPoly d) 3 (8 * Real.sqrt d) R
      (cubicCompConst d) := by
  intro w hw ρ ρ' hXρ hρρ' _
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨t, ht, htr, hq⟩ := hw
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hXρ
  have hρ' : 8 * Real.sqrt d ≤ ρ' := hXρ.trans hρρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by have := Real.sqrt_pos.2 (Nat.cast_pos.2 hd); positivity)
    hρ'
  set T := ∑ i, ∑ j, ∑ k, |t i j k| with hT
  have hT0 : 0 ≤ T := by positivity
  have hK := mixedThirdConst_pos hd
  have hup := ballExcess_cubicPoly_le z hρ0 ht htr hq
  have hlow : T * ρ' ^ 3 / (d ^ 3 * mixedThirdConst d) ≤
      ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicQuadratic d) ρ'
        w := by
    apply le_ballExcess
    intro h hh
    have hGq : (fun x => (w - h) x - cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈
        clusterQuadratic (latticeComponent d) := by
      convert (clusterQuadratic (latticeComponent d)).sub_mem hq.1 hh.1 using 1
      funext x
      simp only [Pi.sub_apply]
      ring
    have hN : componentBallSeminorm (latticeComponent d) z ρ' (w - h) =
        componentBallL2 (latticeComponent d) z ρ' (fun x => latticeExt (w - h) x.val) := by
      rw [componentBallSeminorm_apply]; rfl
    rw [hN, div_le_iff₀ (by positivity)]
    set N := componentBallL2 (latticeComponent d) z ρ' (fun x => latticeExt (w - h) x.val)
    have hb : ∀ i j k, |t i j k| * ρ' ^ 3 ≤ mixedThirdConst d * N := fun i j k =>
      le_componentBallL2_of_fwd3 z hρ' (latticeExt (w - h)) i j k (t i j k)
        (fun y => fwd_fwd_fwd_latticeExt ht hGq i j k y)
    calc T * ρ' ^ 3 = ∑ i, ∑ j, ∑ k, |t i j k| * ρ' ^ 3 := by
          rw [hT]; simp only [sum_mul]
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, ∑ _k : Fin d, mixedThirdConst d * N :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => hb i j k
      _ = N * (d ^ 3 * mixedThirdConst d) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc _ ≤ T * ρ ^ 3 / 6 := hup
    _ = cubicCompConst d * (ρ / ρ') ^ 3 * (T * ρ' ^ 3 / (d ^ 3 * mixedThirdConst d)) := by
        rw [cubicCompConst]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by
        rw [cubicCompConst]; exact mul_nonneg (div_nonneg (by positivity) (by norm_num))
          (pow_nonneg (div_nonneg hρ0 hρ'0.le) 3))

end Rigidity.Proofs.Regularity
