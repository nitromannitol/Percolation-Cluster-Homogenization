import PercolationClusterHomogenization.Proofs.Cluster.GeneralFieldPairing
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessNu
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessTools

/-!
# Display (5.33) of Armstrong and Dario: flatness of the coarsened maximizers of `ν`, in every
dimension

Let `ā` be the homogenized matrix, `ξ = ā⁻¹ q`, `v = v(·, □_{n+1}, ξ)` the maximizer of
`ν(□_{n+1}, ξ)` (zero off the resolution of the cube) and `w = [v]_𝒫` its coarsening. Taking the
expectation of the pointwise bound `exists_cubeNuFlatness_le_pointwise` with `c_k = ξ` and with the
coarse scale `n₀ = ⌈(n + 1)/2⌉` (or `n₀ = n + 1` for the cubes of scale less than `4d`), and
inserting

* the energy of the coarsened maximizer, display (4.25) in expectation
  (`exists_lintegral_coarse_cubeNuSolution_le` with the exponent `2d`),
* Lemma 5.5 for `ν` at the scales `k ∈ [n₀, n + 1)` (`exists_lintegral_cubeNuRestrictError_le`),
* display (4.26) in `L²(P)` on the subcubes of scale `k` (`exists_lintegral_cubeNuGradAvg_sub_le`),

gives (`exists_lintegral_cubeNuFlatness_le`)

`E[‖w - ℓ_ξ - (w - ℓ_ξ)_{□_{n+1}}‖²_{L̲²(□_{n+1})}]
  ≤ C |q|² 3^{2n} (3^{-n/4} + 3^{-n} ∑_{k=0}^{n} 3^k τ_k)`.

The expectation of the pointwise bound is a sum of expectations, for which the random variables
are measurable: the difference of the coarsened maximizer of `ν` across an edge of the cube is the
pairing with the field supported on that edge, hence a combination of the measurable quantities
`1{partition event, V resolved} μ_{g,p}(V)` by polarization (`measurable_cubeNuSolution_edge`), and
the energy, the quantity of display (5.12) and the spatial averages of the coarsened gradient are
finite combinations of these differences (`aemeasurable_cubeCoarseEnergy_cubeNuSolution`,
`aemeasurable_cubeNuRestrictError`, `aemeasurable_cubeNuGradAvg`). This is the general-dimensional
form of `Rigidity.Percolation.exists_lintegral_planarNuFlatness_le`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aemeasurable_ite_of_prop {P : Prop} [Decidable P] {f g : Ω → ℝ}
    (hf : P → AEMeasurable f μ) (hg : ¬P → AEMeasurable g μ) :
    AEMeasurable (fun ω => if P then f ω else g ω) μ := by
  by_cases h : P
  · exact (hf h).congr (Filter.Eventually.of_forall fun ω => by simp only [h, if_true])
  · exact (hg h).congr (Filter.Eventually.of_forall fun ω => by simp only [h, if_false])

/-- The pairing of a fixed field with the gradient of a random function is measurable when the
differences of the function across the edges of the domain are. -/
theorem aemeasurable_latticeEdgePairing_of_edge (D : Finset (Vertex d))
    (g : Vertex d → Fin d → ℝ) {F : Ω → Vertex d → ℝ}
    (hF : ∀ x ∈ D, ∀ i : Fin d, x + LatticeProb.unit i ∈ D →
      AEMeasurable (fun ω => F ω (x + LatticeProb.unit i) - F ω x) μ) :
    AEMeasurable (fun ω => latticeEdgePairing D g (F ω)) μ := by
  unfold latticeEdgePairing
  refine Finset.aemeasurable_fun_sum _ fun x hx => Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact aemeasurable_ite_of_prop (fun hxi => (hF x hx i hxi).const_mul _)
    fun _ => aemeasurable_const

/-- The squared gradient of a random function, summed over the domain, is measurable when the
differences of the function across the edges of the domain are. -/
theorem aemeasurable_sum_gradNormSq_of_edge (D : Finset (Vertex d)) {F : Ω → Vertex d → ℝ}
    (hF : ∀ x ∈ D, ∀ i : Fin d, x + LatticeProb.unit i ∈ D →
      AEMeasurable (fun ω => F ω (x + LatticeProb.unit i) - F ω x) μ) :
    AEMeasurable (fun ω => ∑ x ∈ D, Rigidity.Proofs.Multiscale.gradNormSq D (F ω) x) μ := by
  refine Finset.aemeasurable_fun_sum _ fun x hx => ?_
  unfold Rigidity.Proofs.Multiscale.gradNormSq
  refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
  have hu : (Rigidity.Proofs.Multiscale.unitVec i : Vertex d) = LatticeProb.unit i := rfl
  rw [hu]
  refine (aemeasurable_ite_of_prop (fun h => ?_) fun _ => aemeasurable_const).add
    (aemeasurable_ite_of_prop (fun h => ?_) fun _ => aemeasurable_const)
  · exact ((hF x hx i h).pow_const 2).congr
      (Filter.Eventually.of_forall fun ω => by beta_reduce; ring)
  · have h' : x - LatticeProb.unit i + LatticeProb.unit i ∈ D := by rwa [sub_add_cancel]
    have h2 := (hF _ h i h').pow_const 2
    simp only [sub_add_cancel] at h2
    exact h2

end Measurability

/-- **Measurability of the coarsened maximizers of `ν` across an edge.** For `x` and `x + eᵢ` in
`V`, the difference `[v(·, V, ξ)]_𝒫(x + eᵢ) - [v(·, V, ξ)]_𝒫(x)` is a measurable function of the
configuration: it is the pairing of `v(·, V, ξ)` with the field supported on the edge, given by
polarization through `μ_{g,p}` on the event that the partition exists and resolves `V`, and zero
off this event. -/
theorem measurable_cubeNuSolution_edge (hd : 0 < d) (V : TriadicCube d) (ξ : Fin d → ℝ)
    {x : Vertex d} {i : Fin d} (hx : x ∈ V.toIntegerCube.vertices)
    (hxi : x + LatticeProb.unit i ∈ V.toIntegerCube.vertices) :
    Measurable fun ω : Configuration d =>
      cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω (x + LatticeProb.unit i)) -
        cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x) := by
  set g : Vertex d → Fin d → ℝ := fun y k => if y = x ∧ k = i then 1 else 0 with hg
  have hpair : ∀ (ω : Configuration d) (u : CubeFun ω V), cubeFieldPairing ω V g u =
      cubeExtend ω V u (partitionAnchor ω (x + LatticeProb.unit i)) -
        cubeExtend ω V u (partitionAnchor ω x) := by
    intro ω u
    rw [cubeFieldPairing_apply, Finset.sum_eq_single_of_mem x hx,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [hg, hxi]
    all_goals intro b _ hb; simp [hg, hb]
  have hpol : ∀ ω : Configuration d, cubeFieldPairing ω V g (cubeNuSolution ω V ξ) =
      -V.latticeVolume *
        ((if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V (g + 0) ξ else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V 0 ξ else 0)) := by
    intro ω
    by_cases hω : PartitionEvent ω ∧ PartitionResolved ω V
    · rw [if_pos hω, if_pos hω, if_pos hω, cubeNuSolution_eq hω.1 hω.2]
      obtain ⟨hv, hfv⟩ := cubeNuMaximizer_spec (ω := ω) V ξ
      exact cubeFieldPairing_eq_cubeMuGen hd hω.1 hω.2 hv
        (fun w hw => by rw [hfv w hw, cubeFieldPairing_zero_field, zero_add]) g
    · rw [if_neg hω, if_neg hω, if_neg hω]
      have h0 : cubeNuSolution ω V ξ = 0 := by rw [cubeNuSolution, if_neg hω]
      rw [h0, map_zero]
      ring
  have hfun : (fun ω : Configuration d =>
      cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω (x + LatticeProb.unit i)) -
        cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) = fun ω =>
      -V.latticeVolume *
        ((if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V (g + 0) ξ else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V 0 ξ else 0)) := by
    funext ω
    rw [← hpair, hpol]
  rw [hfun]
  exact (((measurable_cubeMuGen_indicator V (g + 0) ξ).sub
    (measurable_cubeMuGen_indicator V g 0)).sub (measurable_cubeMuGen_indicator V 0 ξ)).const_mul _

variable {p : unitInterval}

theorem aemeasurable_cubeCoarseEnergy_cubeNuSolution (hd : 0 < d) (V : TriadicCube d)
    (ξ : Fin d → ℝ) :
    AEMeasurable (fun ω => cubeCoarseEnergy ω V (cubeNuSolution ω V ξ)) (latticeBondLaw d p) := by
  unfold cubeCoarseEnergy
  exact (aemeasurable_sum_gradNormSq_of_edge
    (F := fun ω x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) _
    fun x hx i hxi => (measurable_cubeNuSolution_edge hd V ξ hx hxi).aemeasurable).const_mul _

theorem aemeasurable_cubeCoarsePairing_cubeNuSolution (hd : 0 < d) (V : TriadicCube d)
    (ξ q : Fin d → ℝ) :
    AEMeasurable (fun ω => cubeCoarsePairing ω V q (cubeNuSolution ω V ξ))
      (latticeBondLaw d p) := by
  simp only [cubeCoarsePairing_eq_latticeEdgePairing]
  exact aemeasurable_latticeEdgePairing_of_edge
    (F := fun ω x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) _ _
    fun x hx i hxi => (measurable_cubeNuSolution_edge hd V ξ hx hxi).aemeasurable

theorem aemeasurable_cubeNuGradAvg (hd : 0 < d) (V : TriadicCube d) (ξ : Fin d → ℝ) (j : Fin d) :
    AEMeasurable (fun ω => cubeNuGradAvg ω V ξ j) (latticeBondLaw d p) := by
  unfold cubeNuGradAvg
  exact (aemeasurable_cubeCoarsePairing_cubeNuSolution hd V ξ (Pi.single j 1)).div_const _

theorem aemeasurable_cubeNuRestrictError (hd : 0 < d) {U : TriadicCube d} {k : ℕ}
    (hk : k ≤ U.scale) (ξ : Fin d → ℝ) :
    AEMeasurable (fun ω => cubeNuRestrictError ω U k ξ) (latticeBondLaw d p) := by
  unfold cubeNuRestrictError cubeRestrictError
  refine (Finset.aemeasurable_fun_sum _ fun V hV =>
    Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
  have hVU := TriadicCube.subset_of_mem_subcubesAt hk hV
  have hsub : ∀ x ∈ V.toIntegerCube.vertices, x ∈ U.toIntegerCube.vertices := fun x hx =>
    (TriadicCube.mem_toIntegerCube_vertices U x).2
      (hVU ((TriadicCube.mem_toIntegerCube_vertices V x).1 hx))
  have h1 := aemeasurable_latticeEdgePairing_of_edge (μ := latticeBondLaw d p)
    (F := fun ω x => cubeExtend ω U (cubeNuSolution ω U ξ) (partitionAnchor ω x))
    V.toIntegerCube.vertices (fun _ => Pi.single i 1)
    fun x hx j hxj => (measurable_cubeNuSolution_edge hd U ξ (hsub x hx) (hsub _ hxj)).aemeasurable
  exact ((h1.sub (aemeasurable_cubeCoarsePairing_cubeNuSolution hd V ξ
    (Pi.single i 1))).div_const _).pow_const 2

/-- `((3^m)^d)^{1/(2d)} = 3^{m/2}`. -/
theorem three_pow_pow_rpow_inv_two_mul (hd : 0 < d) (m : ℕ) :
    (((3 : ℝ) ^ m) ^ d) ^ (1 / ((2 * d : ℕ) : ℝ)) = (3 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

/-- `3^m 3^{3m/4} ≤ 9 · 9^n 3^{-n/4}` for `m = n + 1`. -/
theorem three_pow_mul_rpow_le_nine_mul (n : ℕ) :
    (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ (3 * ((n + 1 : ℕ) : ℝ) / 4) ≤
      9 * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have e1 : (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ (3 * ((n + 1 : ℕ) : ℝ) / 4) =
      (3 : ℝ) ^ ((7 * (n : ℝ) + 7) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have e2 : 9 * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4)) = (3 : ℝ) ^ ((7 * (n : ℝ) + 8) / 4) := by
    have h9 : (9 : ℝ) ^ n = (3 : ℝ) ^ (((2 * n : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast, pow_mul]
      norm_num
    have h9' : (9 : ℝ) = (3 : ℝ) ^ (((2 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
      norm_num
    rw [h9, ← Real.rpow_add (by norm_num)]
    rw [h9', ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The energy term of the proof of (5.33): `3^{2n₀} 3^{(n+1)/2} ≤ 27 · 3^{3d} 9^n 3^{-n/4}` when
`8 n₀ + 2 (n + 1) ≤ 12 + 12 d + 7 n`. -/
theorem three_pow_mul_rpow_le_of_le {n n₀ : ℕ}
    (h : 4 * (2 * n₀) + 2 * (n + 1) ≤ 12 + 12 * d + 7 * n) :
    (3 : ℝ) ^ (2 * n₀) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) ≤
      27 * 3 ^ (3 * d) * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have e1 : (3 : ℝ) ^ (2 * n₀) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) =
      (3 : ℝ) ^ ((2 * (n₀ : ℝ)) + ((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have e2 : 27 * 3 ^ (3 * d) * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4)) =
      (3 : ℝ) ^ ((3 : ℝ) + 3 * d + 7 * (n : ℝ) / 4) := by
    have h9n : (9 : ℝ) ^ n = (3 : ℝ) ^ (2 * n) := by
      rw [pow_mul]
      norm_num
    have h27 : (27 : ℝ) * 3 ^ (3 * d) * (9 : ℝ) ^ n =
        (3 : ℝ) ^ (((3 + 3 * d + 2 * n : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast, h9n, pow_add, pow_add]
      norm_num
    rw [← mul_assoc, h27, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [e1, e2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h' : ((4 * (2 * n₀) + 2 * (n + 1) : ℕ) : ℝ) ≤ ((12 + 12 * d + 7 * n : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- **The arithmetic of the proof of (5.33).** -/
theorem cubeNuFlatness_arith {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) {CM CE C55 CB K L Q Ξ₁ Ξ₂ : ℝ}
    (hCM : 0 ≤ CM) (hCE : 0 ≤ CE) (hC55 : 0 ≤ C55) (hCB : 0 ≤ CB) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hQ : 0 ≤ Q) (hΞ₂ : 0 ≤ Ξ₂) (hΞ₂₁ : Ξ₂ ≤ Ξ₁) (hΞ₁ : Ξ₁ ≤ K * Q) {n n₀ : ℕ}
    (hE : (3 : ℝ) ^ (2 * n₀) * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) ≤
      L * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4)))
    {Zc : ℕ → ℝ} (hZ : ∀ k, Zc k = 0) :
    CM * (3 : ℝ) ^ (2 * n₀) * (CE * Ξ₁ * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) +
      ∑ k ∈ Finset.Ico n₀ (n + 1), 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (C55 * Q * (∑ l ∈ Finset.Ico k (n + 1), τ l + (3 : ℝ) ^ (-(k : ℝ) / 4)) +
          CB * Ξ₁ / 3 ^ k) +
      (CM * (3 : ℝ) ^ (2 * n₀) * Ξ₂ + ∑ k ∈ Finset.Ico n₀ (n + 1),
        CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k * (3 * Zc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ₂)) ≤
      (CM * (CE + 1) * K * L + 9 * (3 * CM * (C55 + CB * K) + CM * K)) * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 4) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * τ k) := by
  set L' : ℝ := 3 * CM * (C55 + CB * K) + CM * K with hL'
  have hL'0 : 0 ≤ L' := by positivity
  set s := Finset.Ico n₀ (n + 1) with hs
  set T : ℕ → ℝ := fun k => ∑ l ∈ Finset.Ico k (n + 1), τ l with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => Finset.sum_nonneg fun l _ => hτ l
  have hρ0 : ∀ k : ℕ, 0 ≤ (3 : ℝ) ^ (-(k : ℝ) / 4) := fun k => by positivity
  have h1ρ : ∀ k : ℕ, 1 ≤ (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4) := by
    intro k
    have e : (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4) = (3 : ℝ) ^ (3 * (k : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    rw [e]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hterm : ∀ k ∈ s, 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (C55 * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4)) + CB * Ξ₁ / 3 ^ k) +
      CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k * (3 * Zc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ₂) ≤
      L' * Q * (3 : ℝ) ^ (n + 1) *
        ((3 : ℝ) ^ k * T k + (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4)) := by
    intro k _
    rw [hZ k]
    set ρ : ℝ := (3 : ℝ) ^ (-(k : ℝ) / 4) with hρ
    set t : ℝ := (3 : ℝ) ^ k with ht
    set M : ℝ := (3 : ℝ) ^ (n + 1) with hM
    have ht0 : 0 < t := by positivity
    have ht0' : t ≠ 0 := ht0.ne'
    have hM0 : 0 ≤ M := by positivity
    have htρ : 1 ≤ t * ρ := h1ρ k
    have hTk := hT0 k
    have hA : t * (CB * Ξ₁ / t) = CB * Ξ₁ := by
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ _ ht0'
    have hB : t * ((t ^ 2)⁻¹ * Ξ₂) ≤ Ξ₂ := by
      have e : t * ((t ^ 2)⁻¹ * Ξ₂) = t⁻¹ * Ξ₂ := by
        rw [sq, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ ht0', one_mul]
      rw [e]
      have hle : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      nlinarith
    have hKQ : Ξ₁ ≤ K * Q * (t * ρ) :=
      hΞ₁.trans (le_mul_of_one_le_right (mul_nonneg hK hQ) htρ)
    have k1 : CB * Ξ₁ ≤ CB * (K * Q * (t * ρ)) := mul_le_mul_of_nonneg_left hKQ hCB
    have k2 : t * ((t ^ 2)⁻¹ * Ξ₂) ≤ K * Q * (t * ρ) := hB.trans (hΞ₂₁.trans hKQ)
    have e1 : 3 * CM * M * t * (C55 * Q * (T k + ρ) + CB * Ξ₁ / t) +
        CM * M * t * (3 * 0 + (t ^ 2)⁻¹ * Ξ₂) =
        3 * CM * M * (C55 * Q * (t * T k + t * ρ)) + 3 * CM * M * (t * (CB * Ξ₁ / t)) +
          CM * M * (t * ((t ^ 2)⁻¹ * Ξ₂)) := by ring
    rw [e1, hA]
    have hc1 : 3 * CM * M * (CB * Ξ₁) ≤ 3 * CM * M * (CB * (K * Q * (t * ρ))) :=
      mul_le_mul_of_nonneg_left k1 (by positivity)
    have hc2 : CM * M * (t * ((t ^ 2)⁻¹ * Ξ₂)) ≤ CM * M * (K * Q * (t * ρ)) :=
      mul_le_mul_of_nonneg_left k2 (by positivity)
    have hrest : 0 ≤ (3 * CM * CB * K + CM * K) * (Q * M * (t * T k)) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hQ hM0) (mul_nonneg ht0.le hTk))
    have e2 : L' * Q * M * (t * T k + t * ρ) =
        3 * CM * M * (C55 * Q * (t * T k + t * ρ)) + 3 * CM * M * (CB * (K * Q * (t * ρ))) +
          CM * M * (K * Q * (t * ρ)) + (3 * CM * CB * K + CM * K) * (Q * M * (t * T k)) := by
      rw [hL']
      ring
    rw [e2]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  set R := ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * τ k with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hτ k)
  have hS1 : ∑ k ∈ s, (3 : ℝ) ^ k * T k ≤ 3 * R := sum_Ico_three_pow_mul_sum_le hτ n₀ (n + 1)
  have hS2 : ∑ k ∈ s, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4) ≤
      (3 : ℝ) ^ (3 * ((n + 1 : ℕ) : ℝ) / 4) :=
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
      fun k _ _ => mul_nonneg (by positivity) (hρ0 k)).trans
      (sum_range_three_pow_mul_rpow_le (n + 1))
  set P : ℝ := (9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 4) with hP
  have hP0 : 0 ≤ P := by positivity
  have hE2 := three_pow_mul_rpow_le_nine_mul n
  have h93 : (3 : ℝ) ^ (n + 1) * (3 * R) = 9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) := by
    have h3n : (3 : ℝ) ^ n ≠ 0 := by positivity
    have e : (3 : ℝ) ^ n * (3 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R) = (3 : ℝ) ^ n * R := by
      rw [mul_assoc, ← mul_assoc ((3 : ℝ) ^ n) _ R, mul_inv_cancel₀ h3n, one_mul]
    rw [show (9 : ℝ) ^ n = (3 : ℝ) ^ n * (3 : ℝ) ^ n by rw [← mul_pow]; norm_num, e, pow_succ]
    ring
  have hsecond : L' * Q * (3 : ℝ) ^ (n + 1) * (∑ k ∈ s, (3 : ℝ) ^ k * T k +
      ∑ k ∈ s, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4)) ≤
      9 * L' * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L' * Q * P := by
    have k1 : (3 : ℝ) ^ (n + 1) * (∑ k ∈ s, (3 : ℝ) ^ k * T k) ≤
        9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) :=
      (mul_le_mul_of_nonneg_left hS1 (by positivity)).trans h93.le
    have k2 : (3 : ℝ) ^ (n + 1) * (∑ k ∈ s, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4)) ≤ 9 * P :=
      (mul_le_mul_of_nonneg_left hS2 (by positivity)).trans hE2
    have hLQ : 0 ≤ L' * Q := mul_nonneg hL'0 hQ
    calc L' * Q * (3 : ℝ) ^ (n + 1) * (∑ k ∈ s, (3 : ℝ) ^ k * T k +
          ∑ k ∈ s, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4))
        = L' * Q * ((3 : ℝ) ^ (n + 1) * (∑ k ∈ s, (3 : ℝ) ^ k * T k)) +
          L' * Q * ((3 : ℝ) ^ (n + 1) *
            (∑ k ∈ s, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4))) := by ring
      _ ≤ L' * Q * (9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R))) + L' * Q * (9 * P) :=
          add_le_add (mul_le_mul_of_nonneg_left k1 hLQ) (mul_le_mul_of_nonneg_left k2 hLQ)
      _ = 9 * L' * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L' * Q * P := by ring
  have hG1 : (1 : ℝ) ≤ (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  set G : ℝ := (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) with hG
  set N : ℝ := (3 : ℝ) ^ (2 * n₀) with hN
  have hN0 : 0 ≤ N := by positivity
  have hfirst : CM * N * (CE * Ξ₁ * G) + CM * N * Ξ₂ ≤ CM * (CE + 1) * K * L * Q * P := by
    have k1 : Ξ₂ ≤ K * Q * G := (hΞ₂₁.trans hΞ₁).trans (le_mul_of_one_le_right (by positivity) hG1)
    have k2 : CE * Ξ₁ * G ≤ CE * (K * Q) * G :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΞ₁ hCE) (by positivity)
    calc CM * N * (CE * Ξ₁ * G) + CM * N * Ξ₂
        ≤ CM * N * (CE * (K * Q) * G) + CM * N * (K * Q * G) :=
          add_le_add (mul_le_mul_of_nonneg_left k2 (by positivity))
            (mul_le_mul_of_nonneg_left k1 (by positivity))
      _ = CM * (CE + 1) * K * Q * (N * G) := by ring
      _ ≤ CM * (CE + 1) * K * Q * (L * P) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = CM * (CE + 1) * K * L * Q * P := by ring
  have hfin : CM * N * (CE * Ξ₁ * G) +
      ∑ k ∈ s, 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (C55 * Q * (T k + (3 : ℝ) ^ (-(k : ℝ) / 4)) + CB * Ξ₁ / 3 ^ k) +
      (CM * N * Ξ₂ + ∑ k ∈ s, CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (3 * Zc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ₂)) ≤
      (CM * (CE + 1) * K * L + 9 * L') * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 4) + ((3 : ℝ) ^ n)⁻¹ * R) := by
    have e : (CM * (CE + 1) * K * L + 9 * L') * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 4) + ((3 : ℝ) ^ n)⁻¹ * R) =
        CM * (CE + 1) * K * L * Q * P + 9 * L' * Q * P +
          (CM * (CE + 1) * K * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) +
            9 * L' * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R))) := by
      rw [hP]
      ring
    have hX : 0 ≤ CM * (CE + 1) * K * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) := by
      positivity
    rw [e]
    linarith
  exact hfin

/-- **Display (5.33) of Armstrong and Dario** (Lemma 5.8 for `ν`), in every dimension `d ≥ 2`, at
the slopes `ā⁻¹ q`: the expected mean square deviation of `[v(·, □_{n+1}, ā⁻¹ q)]_𝒫` from the
affine function of slope `ā⁻¹ q` is at most `C |q|² 9^n (3^{-n/4} + 3^{-n} ∑_{k ≤ n} 3^k τ_k)`. -/
theorem exists_lintegral_cubeNuFlatness_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (cubeFlatnessError ⟨n + 1, 0⟩
          (fun x => cubeExtend ω ⟨n + 1, 0⟩
            (cubeNuSolution ω ⟨n + 1, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q)) (partitionAnchor ω x))
          ((cubeAhom p)⁻¹ *ᵥ q)) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * (9 : ℝ) ^ n *
          ((3 : ℝ) ^ (-(n : ℝ) / 4) +
            ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨CE, hCE, hEn⟩ := exists_lintegral_coarse_cubeNuSolution_le hd hpc (a := 2 * d)
    (by omega)
  obtain ⟨C55, hC55, h55⟩ := exists_lintegral_cubeNuRestrictError_le hd hpc
  obtain ⟨CB, hCB, hB⟩ := exists_lintegral_cubeNuGradAvg_sub_le hd hpc
  obtain ⟨CM, hCM, hpw⟩ := exists_cubeNuFlatness_le_pointwise (d := d)
  set B := (cubeAhom (d := d) p)⁻¹ with hBdef
  set SB := ∑ i, ∑ j, |B i j| with hSB
  have hSB0 : 0 ≤ SB := by positivity
  set K : ℝ := SB ^ 2 * d with hK
  have hK0 : 0 ≤ K := by positivity
  set L : ℝ := 27 * 3 ^ (3 * d) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨CM * (CE + 1) * K * L + 9 * (3 * CM * (C55 + CB * K) + CM * K), by positivity,
    fun n q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  set ξ := B *ᵥ q with hξ
  set Q := ∑ i, q i ^ 2 with hQdef
  set Ξ₁ := (∑ i, |ξ i|) ^ 2 with hΞ₁def
  set Ξ₂ := ∑ i, ξ i ^ 2 with hΞ₂def
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hΞ₁0 : 0 ≤ Ξ₁ := sq_nonneg _
  have hΞ₂0 : 0 ≤ Ξ₂ := Finset.sum_nonneg fun i _ => sq_nonneg (ξ i)
  have hΞ₂₁ : Ξ₂ ≤ Ξ₁ := sum_sq_le_sq_sum_abs_vec ξ
  have hΞ₁K : Ξ₁ ≤ K * Q := by
    have h1 := sum_abs_mulVec_le B q
    have h2 := sq_sum_abs_le_card_mul q
    have h3 : (0 : ℝ) ≤ ∑ i, |ξ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    calc Ξ₁ ≤ (SB * ∑ i, |q i|) ^ 2 := pow_le_pow_left₀ h3 h1 2
      _ = SB ^ 2 * (∑ i, |q i|) ^ 2 := by ring
      _ ≤ SB ^ 2 * (d * Q) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = K * Q := by rw [hK]; ring
  obtain ⟨n₀, hn₀a, hn₀m, hks, hn₀E⟩ : ∃ n₀ : ℕ, n + 1 ≤ 2 * n₀ ∧ n₀ ≤ n + 1 ∧
      (∀ k, n₀ ≤ k → k < n + 1 → 2 * d ≤ k ∧ n + 1 ≤ 2 * k) ∧
      4 * (2 * n₀) + 2 * (n + 1) ≤ 12 + 12 * d + 7 * n := by
    by_cases h : n + 1 < 4 * d
    · exact ⟨n + 1, by omega, le_rfl, fun k h1 h2 => by omega, by omega⟩
    · exact ⟨(n + 2) / 2, by omega, by omega, fun k h1 h2 => by omega, by omega⟩
  have hn₀2 : ((n + 1 : ℕ) : ℝ) / 2 ≤ n₀ := by
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n₀ : ℕ) : ℝ) := by exact_mod_cast hn₀a
    push_cast at this ⊢
    linarith
  set s := Finset.Ico n₀ (n + 1) with hs
  have hvol : U.latticeVolume = ((3 : ℝ) ^ (n + 1)) ^ d := rfl
  have hvol0 := U.latticeVolume_pos
  have hvne : U.latticeVolume ≠ 0 := hvol0.ne'
  have I₀ : ∫⁻ ω, ENNReal.ofReal (cubeCoarseEnergy ω U (cubeNuSolution ω U ξ)) ∂μ ≤
      ENNReal.ofReal (CE * Ξ₁ * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
    have hpt : ∀ ω, ENNReal.ofReal (cubeCoarseEnergy ω U (cubeNuSolution ω U ξ)) =
        ENNReal.ofReal U.latticeVolume⁻¹ * ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeNuSolution ω U ξ) (partitionAnchor ω x)) x ^ 2) := by
      intro ω
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hvol0.le), cubeCoarseEnergy]
      congr 2
      exact Finset.sum_congr rfl fun x _ => gradNormSq_eq_gradNormIn_sq_general _ _ x
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal U.latticeVolume⁻¹ * ∫⁻ ω, ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
            (fun x => cubeExtend ω U (cubeNuSolution ω U ξ) (partitionAnchor ω x)) x ^ 2) ∂μ
        ≤ ENNReal.ofReal U.latticeVolume⁻¹ * ENNReal.ofReal (CE * Ξ₁ * U.latticeVolume *
            U.latticeVolume ^ (1 / ((2 * d : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hEn U ξ) zero_le
      _ = ENNReal.ofReal (CE * Ξ₁ * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hvol0.le)]
          congr 1
          have hr : U.latticeVolume ^ (1 / ((2 * d : ℕ) : ℝ)) =
              (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) := by
            rw [hvol]
            exact three_pow_pow_rpow_inv_two_mul hd0 (n + 1)
          rw [hr, show U.latticeVolume⁻¹ * (CE * Ξ₁ * U.latticeVolume *
              (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2)) = CE * Ξ₁ * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2) *
              (U.latticeVolume⁻¹ * U.latticeVolume) by ring, inv_mul_cancel₀ hvne, mul_one]
  have If : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal (cubeNuRestrictError ω U k ξ) ∂μ ≤
      ENNReal.ofReal (C55 * Q * (∑ l ∈ Finset.Ico k (n + 1), cubeTau (d := d) p l +
        (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    obtain ⟨h3, h4⟩ := hks k h1 h2
    rw [three_rpow_neg_div_four_eq]
    exact h55 k (n + 1) q h3 h2 h4
  have hne : ∀ k ≤ n + 1, (U.subcubesAt k).Nonempty := fun k hk => by
    rw [← Finset.card_pos, hU, card_subcubesAt_eq_general hk,
      Rigidity.Proofs.Multiscale.card_centers hk]
    positivity
  have Ig : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal ((((U.subcubesAt k).card : ℝ))⁻¹ *
      ∑ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeNuGradAvg ω V ξ j - ξ j) ^ 2) ∂μ ≤
      ENNReal.ofReal (CB * Ξ₁ / 3 ^ k) := by
    intro k hk
    refine lintegral_ofReal_avg_le (hne k (Finset.mem_Ico.1 hk).2.le)
      (fun V _ ω => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (fun V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
        ((aemeasurable_cubeNuGradAvg hd0 V ξ j).sub_const _).pow_const 2) fun V hV => ?_
    have h := hB V ξ
    rw [TriadicCube.scale_of_mem_subcubesAt hV] at h
    exact h
  have hf : ∀ k ∈ s, ∀ ω, 0 ≤ cubeNuRestrictError ω U k ξ := fun k _ ω =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hg : ∀ k ∈ s, ∀ ω, 0 ≤ (((U.subcubesAt k).card : ℝ))⁻¹ *
      ∑ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeNuGradAvg ω V ξ j - ξ j) ^ 2 := fun k _ ω =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have mf : ∀ k ∈ s, AEMeasurable (fun ω => cubeNuRestrictError ω U k ξ) μ := fun k hk =>
    aemeasurable_cubeNuRestrictError hd0 (show k ≤ n + 1 from (Finset.mem_Ico.1 hk).2.le) ξ
  have mg : ∀ k ∈ s, AEMeasurable (fun ω => (((U.subcubesAt k).card : ℝ))⁻¹ *
      ∑ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeNuGradAvg ω V ξ j - ξ j) ^ 2) μ := fun k _ =>
    (Finset.aemeasurable_fun_sum _ fun V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      ((aemeasurable_cubeNuGradAvg hd0 V ξ j).sub_const _).pow_const 2).const_mul _
  have hmain := lintegral_ofReal_le_of_le (μ := μ)
    (X := fun ω => cubeFlatnessError U (fun x => cubeExtend ω U (cubeNuSolution ω U ξ)
      (partitionAnchor ω x)) ξ)
    (f₀ := fun ω => cubeCoarseEnergy ω U (cubeNuSolution ω U ξ))
    (f := fun k ω => cubeNuRestrictError ω U k ξ)
    (g := fun k ω => (((U.subcubesAt k).card : ℝ))⁻¹ *
      ∑ V ∈ U.subcubesAt k, ∑ j : Fin d, (cubeNuGradAvg ω V ξ j - ξ j) ^ 2)
    (s := s) (a₀ := CM * (3 : ℝ) ^ (2 * n₀))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (3 : ℝ) ^ (2 * n₀) * Ξ₂ + ∑ k ∈ s, CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
      (3 * ∑ j : Fin d, (ξ j - ξ j) ^ 2 + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ₂))
    (b₀ := CE * Ξ₁ * (3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 2))
    (bf := fun k => C55 * Q * (∑ l ∈ Finset.Ico k (n + 1), cubeTau (d := d) p l +
      (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => CB * Ξ₁ / 3 ^ k)
    (by positivity) (fun k _ => by positivity) (by positivity)
    (fun ω => cubeCoarseEnergy_nonneg _ _) hf hg
    (aemeasurable_cubeCoarseEnergy_cubeNuSolution hd0 U ξ) mf mg
    (fun ω => hpw (n + 1) n₀ hn₀2 hn₀m ω ξ ξ (fun _ => ξ)) I₀ If Ig (by positivity)
    (fun k _ => mul_nonneg (mul_nonneg hC55 hQ0)
      (add_nonneg (Finset.sum_nonneg fun l _ => cubeTau_nonneg p l) (by positivity)))
    (fun k _ => by positivity)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact cubeNuFlatness_arith (τ := cubeTau (d := d) p) (cubeTau_nonneg p) hCM hCE hC55 hCB hK0
    hL0 hQ0 hΞ₂0 hΞ₂₁ hΞ₁K (three_pow_mul_rpow_le_of_le hn₀E)
    (Zc := fun _ => ∑ j : Fin d, (ξ j - ξ j) ^ 2) fun k => by simp

end Rigidity.Percolation
