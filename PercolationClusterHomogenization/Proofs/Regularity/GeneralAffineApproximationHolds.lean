import PercolationClusterHomogenization.Proofs.Regularity.GeneralAffineFromNu

/-!
# The approximation of affine functions on growing balls of the cluster of `ℤᵈ`, and the corrected
planes

`cubeAffineApproximationAe_holds` proves `CubeAffineApproximationAe d`, the input of Step 3 of
Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1) for `k = 1`, in every dimension
`d ≥ 2`, from the almost sure flatness of the maximizers of `ν` at all large scales
(`ae_eventually_cubeNuFlatness_le`, from (5.33) of Armstrong and Dario, arXiv:1609.09431v2), the
minimal scales of Proposition 2.4 (`cubeMinimalScales_holds` with the exponent `t = 2d²`, so that
the partition cubes of `□_{j+3}` have sides at most `3^{(j+3)/(2d+1)}`) and the density of the
cluster, by the approximation at one scale (`affineApproximation_at_scale`) and the arithmetic of
`affine_scale_arith`. With `correctorSublinearL2Ae_of_affineApproximationAe` and
`correctedPlaneExistence_of_sublinearL2Ae` this gives (1.18) with an almost surely finite scale
(`correctorSublinearL2Ae_holds`) and the corrected planes (`correctedPlaneExistence_holds`,
Theorem 2 (ii) at `k = 1`) in every dimension `d ≥ 2`, with no hypothesis.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2
open scoped Matrix Classical

variable {d : ℕ}

/-- **The arithmetic of the approximation at the scale `3^{j+1}`.** -/
theorem affine_scale_arith {E Q₁ Q₂ K κ κ' Λ μ δ Z Fl Vol : ℝ} {j : ℕ} (hE : 1 ≤ E)
    (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hQ : Q₂ ≤ Q₁ ^ 2) (hκ : 0 < κ) (hκ' : 0 < κ') (hΛ : 0 ≤ Λ)
    (hδ2 : δ ≤ 1 / 2) (hμj : μ ^ j ≤ E ^ (-2 * δ)) (hμ0 : 0 ≤ μ)
    (hVol : Vol = 27 ^ d * E ^ d) (hFl : Fl ≤ 81 * Λ * E ^ 2 * μ ^ j)
    (hZ2 : Z ^ (2 * d) ≤ 27 * E) (hκE : κ * E ^ d ≤ 3 ^ (d * d) * κ') :
    Real.sqrt (2 * (d * Vol * (Q₂ * Fl) + d * Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2 * Vol))) /
        κ') ≤
      Real.sqrt (2 * (2 * d * 27 ^ d * 3 ^ (d * d) / κ * (81 * Λ + 27 * K ^ 2 * 3 ^ d / 2))) *
        Q₁ * (3 * E) ^ (1 - δ) := by
  have hE0 : 0 < E := by linarith
  set c₀ := 2 * d * 27 ^ d * 3 ^ (d * d) / κ * (81 * Λ + 27 * K ^ 2 * 3 ^ d / 2) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set X := 81 * Λ * E ^ 2 * μ ^ j + 27 * K ^ 2 * 3 ^ d / 2 * E with hX
  -- the numerator
  have hN : 2 * (d * Vol * (Q₂ * Fl) + d * Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2 * Vol))) ≤
      2 * d * 27 ^ d * E ^ d * Q₂ * X := by
    rw [hVol]
    have h1 : Q₂ * Fl ≤ Q₂ * (81 * Λ * E ^ 2 * μ ^ j) := mul_le_mul_of_nonneg_left hFl hQ₂
    have h2 : Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2)) ≤ Q₂ * (K ^ 2 * (27 * E) * (3 ^ d / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hQ₂
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ2 (sq_nonneg K)) (by positivity)
    have hA : (0 : ℝ) ≤ 2 * d * 27 ^ d * E ^ d := by positivity
    calc 2 * (d * (27 ^ d * E ^ d) * (Q₂ * Fl) +
          d * Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2 * (27 ^ d * E ^ d))))
        = 2 * d * 27 ^ d * E ^ d * (Q₂ * Fl + Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2))) := by ring
      _ ≤ 2 * d * 27 ^ d * E ^ d * (Q₂ * (81 * Λ * E ^ 2 * μ ^ j) +
            Q₂ * (K ^ 2 * (27 * E) * (3 ^ d / 2))) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA
      _ = 2 * d * 27 ^ d * E ^ d * Q₂ * X := by rw [hX]; ring
  -- the bracket
  have hX' : X ≤ (81 * Λ + 27 * K ^ 2 * 3 ^ d / 2) * (2 * E ^ (2 - 2 * δ)) := by
    have h1 : E ^ 2 * μ ^ j ≤ E ^ (2 - 2 * δ) := by
      calc E ^ 2 * μ ^ j ≤ E ^ (2 : ℝ) * E ^ (-2 * δ) := by
            rw [Real.rpow_two]; exact mul_le_mul_of_nonneg_left hμj (by positivity)
        _ = E ^ (2 - 2 * δ) := by rw [← Real.rpow_add hE0]; ring_nf
    have h2 : E ≤ E ^ (2 - 2 * δ) := by
      calc E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
        _ ≤ E ^ (2 - 2 * δ) := Real.rpow_le_rpow_of_exponent_le hE (by linarith)
    have hp : (0 : ℝ) ≤ E ^ (2 - 2 * δ) := by positivity
    have hK : 0 ≤ 27 * K ^ 2 * 3 ^ d / 2 := by positivity
    have hL : 0 ≤ 81 * Λ := by positivity
    calc X = 81 * Λ * (E ^ 2 * μ ^ j) + 27 * K ^ 2 * 3 ^ d / 2 * E := by rw [hX]; ring
      _ ≤ 81 * Λ * E ^ (2 - 2 * δ) + 27 * K ^ 2 * 3 ^ d / 2 * E ^ (2 - 2 * δ) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hL) (mul_le_mul_of_nonneg_left h2 hK)
      _ ≤ (81 * Λ + 27 * K ^ 2 * 3 ^ d / 2) * (2 * E ^ (2 - 2 * δ)) := by nlinarith
  have hX0 : 0 ≤ X := by positivity
  -- the division by `κ'`
  have hEκ : E ^ d / κ' ≤ 3 ^ (d * d) / κ := by
    rw [div_le_div_iff₀ hκ' hκ]; linarith
  have hdiv : 2 * d * 27 ^ d * E ^ d * Q₂ * X / κ' ≤ 2 * c₀ * Q₂ * E ^ (2 - 2 * δ) := by
    have e : 2 * d * 27 ^ d * E ^ d * Q₂ * X / κ' = 2 * d * 27 ^ d * Q₂ * X * (E ^ d / κ') := by
      ring
    rw [e]
    calc 2 * d * 27 ^ d * Q₂ * X * (E ^ d / κ') ≤ 2 * d * 27 ^ d * Q₂ * X * (3 ^ (d * d) / κ) :=
          mul_le_mul_of_nonneg_left hEκ (by positivity)
      _ ≤ 2 * d * 27 ^ d * Q₂ * ((81 * Λ + 27 * K ^ 2 * 3 ^ d / 2) * (2 * E ^ (2 - 2 * δ))) *
            (3 ^ (d * d) / κ) := by gcongr
      _ = 2 * c₀ * Q₂ * E ^ (2 - 2 * δ) := by rw [hc₀]; ring
  -- the square root
  have h3E : E ^ (2 - 2 * δ) ≤ ((3 * E) ^ (1 - δ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    calc E ^ (2 - 2 * δ) ≤ (3 * E) ^ (2 - 2 * δ) :=
          Real.rpow_le_rpow hE0.le (by linarith) (by linarith)
      _ = (3 * E) ^ ((1 - δ) * ((2 : ℕ) : ℝ)) := by norm_num; ring_nf
  rw [Real.sqrt_le_left (by positivity)]
  calc 2 * (d * Vol * (Q₂ * Fl) + d * Q₂ * (K ^ 2 * Z ^ (2 * d) * (3 ^ d / 2 * Vol))) / κ'
      ≤ 2 * d * 27 ^ d * E ^ d * Q₂ * X / κ' := div_le_div_of_nonneg_right hN hκ'.le
    _ ≤ 2 * c₀ * Q₂ * E ^ (2 - 2 * δ) := hdiv
    _ ≤ 2 * c₀ * Q₁ ^ 2 * ((3 * E) ^ (1 - δ)) ^ 2 := by gcongr
    _ = (Real.sqrt (2 * c₀) * Q₁ * (3 * E) ^ (1 - δ)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]

/-- **The approximation of affine functions on growing balls of the infinite cluster of `ℤᵈ`**,
`d ≥ 2`, almost surely above a finite scale, with no hypothesis. -/
theorem cubeAffineApproximationAe_holds [NeZero d] (hd : 2 ≤ d) : CubeAffineApproximationAe d := by
  intro p hpc hp1
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  obtain ⟨μ, hμ0, hμ1, hfl⟩ := ae_eventually_cubeNuFlatness_le hd hpc
  set ae : Fin d → Fin d → ℝ := fun i => cubeAhom p *ᵥ Pi.single i 1 with hae
  set Λ : ℝ := ∑ i, (∑ k, ae i k ^ 2 + 1) with hΛdef
  have hΛi : ∀ i, ∑ k, ae i k ^ 2 + 1 ≤ Λ := fun i =>
    Finset.single_le_sum (f := fun i => ∑ k, ae i k ^ 2 + 1) (fun i _ => by positivity)
      (Finset.mem_univ i)
  have hΛ0 : 0 ≤ Λ := by positivity
  -- the exponent `δ`
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log μ⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hμ0, hμ1⟩)
  set δ : ℝ := min (Real.log μ⁻¹ / (2 * Real.log 3)) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hμ3 : μ ≤ (3 : ℝ) ^ (-2 * δ) := by
    have e : (3 : ℝ) ^ (-2 * (Real.log μ⁻¹ / (2 * Real.log 3))) = μ := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.log_inv]
      rw [show Real.log 3 * (-2 * (-Real.log μ / (2 * Real.log 3))) = Real.log μ by
        field_simp]
      exact Real.exp_log hμ0
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have : δ ≤ Real.log μ⁻¹ / (2 * Real.log 3) := min_le_left _ _; linarith)
  -- the minimal scales, with `t = 2 d²`
  obtain ⟨s₅, C₅, -, -, M₅, -, -, -, hM₅ae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc (2 * (d : ℝ) ^ 2) (by nlinarith)
  -- the density of the cluster
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) ((d : ℝ) + 1)
  obtain ⟨M₄, -, -, -, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  refine ⟨δ, Real.sqrt (2 * (2 * d * 27 ^ d * 3 ^ (d * d) / κ *
    (81 * Λ + 27 * coarseErrorConst d ^ 2 * 3 ^ d / 2))), hδ0, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [ae_all_iff.2 (fun i => hfl (ae i)), hM₅ae, hM₄ae, ae_partitionEvent hd hpc] with
    ω hωfl hω₅ hω₄ hP
  intro h q
  have hinf := uniqueInfiniteComponent_infinite h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hωfl)
  obtain ⟨ma, hma⟩ := eventually_le_three_pow (max (M₅ ω) (3 ^ d * M₄ ω))
  refine ⟨max (max N ma) (d + 2) + 1, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hjN : N ≤ j + 2 := by omega
  have hjma : ma ≤ j := by omega
  have hjd : d + 2 ≤ j := by omega
  set E : ℝ := (3 : ℝ) ^ j with hEdef
  have hE1 : 1 ≤ E := one_le_pow₀ (by norm_num)
  have hE0 : 0 < E := by linarith
  have hEm := hma j hjma
  have hM₅ : M₅ ω ≤ 3 ^ (j + 3) :=
    ((le_max_left _ _).trans hEm).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hM₄ : M₄ ω ≤ 3 ^ (j - d) := by
    have h1 : 3 ^ d * M₄ ω ≤ 3 ^ j := (le_max_right _ _).trans hEm
    have e : (3 : ℝ) ^ j = 3 ^ d * 3 ^ (j - d) := by rw [← pow_add]; congr 1; omega
    rw [e] at h1
    exact le_of_mul_le_mul_left h1 (by positivity)
  -- the sizes of the partition cubes of `□_{j+3}`
  set α : ℝ := (d : ℝ) * ((j + 3 : ℕ) : ℝ) / (d + 2 * (d : ℝ) ^ 2) with hαdef
  have hαe : α = ((j : ℝ) + 3) / (1 + 2 * d) := by
    rw [hαdef]; push_cast; field_simp
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hdj : (2 : ℝ) ≤ d * j := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hαj : α ≤ j := by
    rw [hαe, div_le_iff₀ (by positivity)]; nlinarith
  have hα2 : α * (2 * d) ≤ j + 3 := by
    rw [hαe, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hscR : ∀ x ∈ (⟨j + 3, 0⟩ : TriadicCube d).vertices,
      (3 : ℝ) ^ (partitionCube ω x).scale ≤ (3 : ℝ) ^ α := fun x hx => (hω₅ (j + 3) hM₅).2 x hx
  have hsc : ∀ x ∈ triadicCubeFinset d (j + 3) 0, (partitionCube ω x).scale ≤ j := by
    intro x hx
    have h1 := hscR x (mem_cubeFinset_iff_vertices.1 hx)
    rw [← Real.rpow_natCast] at h1
    have h2 := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).1 h1
    exact_mod_cast h2.trans hαj
  have hres : PartitionResolved ω ⟨j + 3, 0⟩ := fun z hz => by
    have := hsc z (mem_cubeFinset_iff_vertices.2 hz)
    show (partitionCube ω z).scale ≤ j + 3
    omega
  have hZ : ∀ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
      (3 : ℝ) ^ (partitionCube ω x).scale ≤ (3 : ℝ) ^ α := fun x hx =>
    hscR x ((TriadicCube.mem_toIntegerCube_vertices _ x).1 (Finset.mem_filter.1 hx).1)
  have hZ2 : ((3 : ℝ) ^ α) ^ (2 * d) ≤ 27 * E := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    calc (3 : ℝ) ^ (α * ((2 * d : ℕ) : ℝ)) ≤ (3 : ℝ) ^ ((j + 3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 27 * E := by rw [Real.rpow_natCast, hEdef]; ring
  -- the flatness at the scale `j + 2`
  set Fl : ℝ := Λ * 9 ^ (j + 2) * μ ^ (j + 2) with hFldef
  have hfl' : ∀ i : Fin d, cubeFlatnessError ⟨j + 3, 0⟩
      (fun x => cubeExtend ω ⟨j + 3, 0⟩ (cubeNuSolution ω ⟨j + 3, 0⟩ (Pi.single i 1))
        (partitionAnchor ω x)) (Pi.single i 1) ≤ Fl := by
    intro i
    have h1 := hN (j + 2) hjN i
    rw [cubeAhom_inv_mulVec_mulVec hd hpc] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hΛi i) (by positivity))
      (by positivity)
  have hFl : Fl ≤ 81 * Λ * E ^ 2 * μ ^ j := by
    have e : (9 : ℝ) ^ (j + 2) = 81 * E ^ 2 := by
      rw [hEdef, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, show 2 * (j + 2) = j * 2 + 4 by ring,
        pow_add]
      norm_num
      ring
    have hμ2 : μ ^ (j + 2) ≤ μ ^ j := pow_le_pow_of_le_one hμ0.le hμ1.le (by omega)
    rw [hFldef, e]
    have : 0 ≤ Λ * (81 * E ^ 2) := by positivity
    calc Λ * (81 * E ^ 2) * μ ^ (j + 2) ≤ Λ * (81 * E ^ 2) * μ ^ j :=
          mul_le_mul_of_nonneg_left hμ2 this
      _ = 81 * Λ * E ^ 2 * μ ^ j := by ring
  -- the cluster in the ball `B_{3^{j+1}}`
  set κ' : ℝ := κ * 3 ^ (d * (j - d)) with hκ'def
  have hκ' : 0 < κ' := by positivity
  have hcard : κ' ≤ (componentEuclideanBall (uniqueInfiniteComponent h) 0
      ((3 : ℝ) ^ (j + 1))).card := by
    have hlow := card_componentEuclideanBall_ge (uniqueInfiniteComponent h) (hω₄ h) hM₄
      (x := (0 : Vertex d)) (a := 0) (fun i => by simp) (by linarith)
    have h2d : (2 * d : ℝ) ≤ 3 ^ (d + 1) := by exact_mod_cast two_mul_le_three_pow_succ d
    have hsub : componentEuclideanBall (uniqueInfiniteComponent h) 0 (2 * d * 3 ^ (j - d)) ⊆
        componentEuclideanBall (uniqueInfiniteComponent h) 0 ((3 : ℝ) ^ (j + 1)) := by
      intro x hx
      rw [mem_componentEuclideanBall] at hx ⊢
      have e : (3 : ℝ) ^ (j + 1) = 3 ^ (d + 1) * 3 ^ (j - d) := by
        rw [← pow_add]; congr 1; omega
      have : (2 * d : ℝ) * 3 ^ (j - d) ≤ 3 ^ (d + 1) * 3 ^ (j - d) :=
        mul_le_mul_of_nonneg_right h2d (by positivity)
      linarith
    exact hlow.trans (by exact_mod_cast Finset.card_le_card hsub)
  have hκE : κ * E ^ d ≤ 3 ^ (d * d) * κ' := by
    have e : E ^ d = 3 ^ (d * d) * 3 ^ (d * (j - d)) := by
      rw [hEdef, ← pow_mul, ← pow_add]; congr 1
      rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega : d ≤ j), mul_comm]
    rw [e, hκ'def]
    apply le_of_eq; ring
  obtain ⟨v, hvH, hvL2⟩ := affineApproximation_at_scale hP (uniqueInfiniteComponent h) hinf
    hres hsc hZ hfl' hκ' hcard q
  refine ⟨v, hvH, hvL2.trans ?_⟩
  have hVol : (⟨j + 3, 0⟩ : TriadicCube d).latticeVolume = 27 ^ d * E ^ d := by
    unfold TriadicCube.latticeVolume
    rw [← mul_pow]
    congr 1
    rw [hEdef]; ring
  have hQ : ∑ i, q i ^ 2 ≤ (∑ i, |q i|) ^ 2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |q i|) fun i _ => abs_nonneg _
    simpa [sq_abs] using h
  have hμj : μ ^ j ≤ E ^ (-2 * δ) := by
    calc μ ^ j ≤ ((3 : ℝ) ^ (-2 * δ)) ^ j := pow_le_pow_left₀ hμ0.le hμ3 j
      _ = E ^ (-2 * δ) := by
          rw [hEdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 3 j,
            ← Real.rpow_mul (by norm_num), mul_comm]
  have harith := affine_scale_arith (d := d) (K := coarseErrorConst d) hE1 (by positivity)
    (by positivity) hQ hκ hκ' hΛ0 hδ2 hμj hμ0.le hVol hFl hZ2 hκE
  have e3 : (3 : ℝ) ^ (j + 1) = 3 * E := by rw [hEdef, pow_succ, mul_comm]
  rw [e3]
  exact harith

/-- **(1.18) on the infinite cluster of `ℤᵈ` with an almost surely finite scale**, `d ≥ 2`, with no
hypothesis. -/
theorem correctorSublinearL2Ae_holds [NeZero d] (hd : 2 ≤ d) : CorrectorSublinearL2Ae d :=
  correctorSublinearL2Ae_of_affineApproximationAe hd (cubeAffineApproximationAe_holds hd)

/-- **Every slope has a corrected plane on the infinite cluster of `ℤᵈ`** (Armstrong and Dario,
Theorem 2 (ii) at `k = 1`), `d ≥ 2`, with no hypothesis. -/
theorem correctedPlaneExistence_holds [NeZero d] (hd : 2 ≤ d) : CorrectedPlaneExistence d :=
  correctedPlaneExistence_of_sublinearL2Ae hd (correctorSublinearL2Ae_holds hd)

end Rigidity.Proofs.Regularity.GeneralDim
