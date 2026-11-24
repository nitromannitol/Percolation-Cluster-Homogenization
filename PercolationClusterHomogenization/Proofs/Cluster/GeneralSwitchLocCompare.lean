import PercolationClusterHomogenization.Proofs.Cluster.GeneralSwitchLocLocal

/-!
# The pointwise comparison of display (5.31) of Armstrong and Dario, in every dimension

For a resolved triadic cube `V` whose partition cubes on the cluster have size at most `W`, the
pairing of the coarsened gradient of a function `w` on the cluster with a field `h` is controlled by
the Dirichlet form: by the Cauchy–Schwarz inequality and Lemma 3.3 with `s = 2`,
`ℓ_h(w)² ≤ K² W^{2d-1} ‖h‖² · 2 B(w, w)` (`cubeFieldPairing_sq_le_of_scale_le`), where
`‖h‖² = ∑_{x ∈ V} ∑ᵢ 1{x + eᵢ ∈ V} h(x, i)²` (`cubeEdgeNormSq`).

If `u` and `u'` solve the first variations `B(·, u) = ℓ_q`, `B(·, u') = ℓ_{q'}` on the harmonic
functions, then by the second variation `B(u - u', u - u') = ℓ_{q - q'}(u - u')` and
`(ℓ_g(u) - ℓ_{g'}(u'))² ≤ 8 K'² (‖g‖² ‖q - q'‖² + ‖g - g'‖² ‖q'‖²)` whenever
`ℓ_h(w)² ≤ K' ‖h‖² · 2 B(w, w)` for all `h, w` (`sq_cubeFieldPairing_sub_le`).

For a triadic cube `V` of scale `n`, a field `g` bounded by `G` and a slope `q` with `∑ᵢ |qᵢ| ≤ Q`,
let `X = |V|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V`. Without any event `|X| ≤ 2d K² 3^{(2d-1)n} G Q`
(`abs_cubeSubcubePairing_le`). On the event `CubeCapGood k V`, with `D` the inner cube at distance
`3^{k+2}` and `u_loc` the solution of the first variation with the field `q|D`, the comparison and
the counting `|V \ D| ≤ 2d 3^{(d-1)n + k + 2}` give
`(X - |V|⁻¹ ℓ_{g|D}(u_loc))² ≤ 576 d³ K⁴ G² Q² 3^{(4d-1)k} / 3ⁿ`
(`sq_sub_cubeSwitchLocValue_le`): the localization step of the proof of Lemma 5.7. The
two-dimensional version is `Rigidity.Proofs.Cluster.sq_sub_switchLocValue_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The squared norm `∑_{x ∈ V} ∑ᵢ 1{x + eᵢ ∈ V} h(x, i)²` of a field over the lattice edges of
`V`. -/
noncomputable def cubeEdgeNormSq (V : TriadicCube d) (h : Vertex d → Fin d → ℝ) : ℝ :=
  ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin d,
    if x + unit i ∈ V.toIntegerCube.vertices then h x i ^ 2 else 0

theorem cubeEdgeNormSq_nonneg (V : TriadicCube d) (h : Vertex d → Fin d → ℝ) :
    0 ≤ cubeEdgeNormSq V h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ite_nonneg (sq_nonneg _) le_rfl

/-- The field pairing is the pairing of the field with the gradient of the coarsening. -/
theorem cubeFieldPairing_eq_latticeEdgePairing (V : TriadicCube d) (h : Vertex d → Fin d → ℝ)
    (w : CubeFun ω V) :
    cubeFieldPairing ω V h w = latticeEdgePairing V.toIntegerCube.vertices h
      (fun x => cubeExtend ω V w (partitionAnchor ω x)) := by
  rw [cubeFieldPairing_apply]
  rfl

/-- **The weighted bound for the field pairing** (Lemma 3.3 with `s = 2`):
`ℓ_h(w)² ≤ K² W^{2d-1} ‖h‖² · 2 B(w, w)`. -/
theorem cubeFieldPairing_sq_le_of_scale_le (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hV : PartitionResolved ω V) {W : ℝ}
    (hW : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (h : Vertex d → Fin d → ℝ) (w : CubeFun ω V) :
    cubeFieldPairing ω V h w ^ 2 ≤
      coarseGradConstant d ^ 2 * W ^ (2 * d - 1) * cubeEdgeNormSq V h * (2 * cubeForm ω V w w) := by
  rw [cubeFieldPairing_eq_latticeEdgePairing]
  have h1 := latticeEdgePairing_sq_le V.toIntegerCube.vertices h
    (fun x => cubeExtend ω V w (partitionAnchor ω x))
  have h2 := latticeEdgeEnergy_le_two_mul_sum_gradNormIn_sq V.toIntegerCube.vertices
    (fun x => cubeExtend ω V w (partitionAnchor ω x))
  have h3 := sum_gradNormIn_coarse_sq_le_cubeForm hd hP hV w hW
  have hN := cubeEdgeNormSq_nonneg V h
  change _ ≤ cubeEdgeNormSq V h * _ at h1
  calc _ ≤ cubeEdgeNormSq V h * latticeEdgeEnergy V.toIntegerCube.vertices
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) := h1
    _ ≤ cubeEdgeNormSq V h * (2 * (coarseGradConstant d ^ 2 * (W ^ (2 * d - 1) *
          cubeForm ω V w w))) :=
        mul_le_mul_of_nonneg_left (h2.trans (by linarith)) hN
    _ = _ := by ring

/-- `B ≤ |X|` and `X² ≤ T · 2B` give `B ≤ 2T`. -/
theorem le_two_mul_of_le_abs_of_sq_le {B X T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (h1 : B ≤ |X|)
    (h2 : X ^ 2 ≤ T * (2 * B)) : B ≤ 2 * T := by
  rcases hB.lt_or_eq with hpos | hzero
  · have h3 : B ^ 2 ≤ X ^ 2 := by
      rw [← sq_abs X]
      exact pow_le_pow_left₀ hB h1 2
    nlinarith
  · rw [← hzero]
    positivity

theorem cubeFieldPairing_sub {U : TriadicCube d} (g h : Vertex d → Fin d → ℝ) (u : CubeFun ω U) :
    cubeFieldPairing ω U (g - h) u = cubeFieldPairing ω U g u - cubeFieldPairing ω U h u := by
  simp only [cubeFieldPairing_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.sub_apply]
    ring
  · ring

/-- **The second variation comparison.** If `u, u'` are harmonic and solve
`B(·, u) = ℓ_q`, `B(·, u') = ℓ_{q'}` on the harmonic functions, and `ℓ_h(w)² ≤ K ‖h‖² · 2 B(w, w)`
for every field `h` and function `w`, then
`(ℓ_g(u) - ℓ_{g'}(u'))² ≤ 8 K² (‖g‖² ‖q - q'‖² + ‖g - g'‖² ‖q'‖²)`. -/
theorem sq_cubeFieldPairing_sub_le {U : TriadicCube d} {g g' q q' : Vertex d → Fin d → ℝ}
    {u u' : CubeFun ω U} (hu : u ∈ cubeHarmonic ω U) (hu' : u' ∈ cubeHarmonic ω U)
    (hv : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeFieldPairing ω U q w)
    (hv' : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u' = cubeFieldPairing ω U q' w)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (h : Vertex d → Fin d → ℝ) (w : CubeFun ω U),
      cubeFieldPairing ω U h w ^ 2 ≤ K * cubeEdgeNormSq U h * (2 * cubeForm ω U w w)) :
    (cubeFieldPairing ω U g u - cubeFieldPairing ω U g' u') ^ 2 ≤
      8 * K ^ 2 * (cubeEdgeNormSq U g * cubeEdgeNormSq U (q - q') +
        cubeEdgeNormSq U (g - g') * cubeEdgeNormSq U q') := by
  have hδA : u - u' ∈ cubeHarmonic ω U := sub_mem hu hu'
  have hBnn : ∀ w : CubeFun ω U, 0 ≤ cubeForm ω U w w := fun w => cubeForm_self_nonneg w
  have hBδ : cubeForm ω U (u - u') (u - u') = cubeFieldPairing ω U (q - q') (u - u') := by
    rw [cubeFieldPairing_sub, ← hv _ hδA, ← hv' _ hδA, ← map_sub]
  have hBδle : cubeForm ω U (u - u') (u - u') ≤ 2 * (K * cubeEdgeNormSq U (q - q')) :=
    le_two_mul_of_le_abs_of_sq_le (X := cubeFieldPairing ω U (q - q') (u - u')) (hBnn _)
      (mul_nonneg hK0 (cubeEdgeNormSq_nonneg _ _)) (by rw [hBδ]; exact le_abs_self _) (hK _ _)
  have hBu' : cubeForm ω U u' u' = cubeFieldPairing ω U q' u' := hv' u' hu'
  have hBu'le : cubeForm ω U u' u' ≤ 2 * (K * cubeEdgeNormSq U q') :=
    le_two_mul_of_le_abs_of_sq_le (X := cubeFieldPairing ω U q' u') (hBnn u')
      (mul_nonneg hK0 (cubeEdgeNormSq_nonneg _ _)) (by rw [hBu']; exact le_abs_self _) (hK _ u')
  have hsplit : cubeFieldPairing ω U g u - cubeFieldPairing ω U g' u' =
      cubeFieldPairing ω U g (u - u') + cubeFieldPairing ω U (g - g') u' := by
    rw [cubeFieldPairing_sub, map_sub]
    ring
  have h1 := hK g (u - u')
  have h2 := hK (g - g') u'
  have hng := cubeEdgeNormSq_nonneg U g
  have hngg := cubeEdgeNormSq_nonneg U (g - g')
  have hnq := cubeEdgeNormSq_nonneg U (q - q')
  have hnq' := cubeEdgeNormSq_nonneg U q'
  rw [hsplit]
  generalize cubeFieldPairing ω U g (u - u') = a at h1 ⊢
  generalize cubeFieldPairing ω U (g - g') u' = b at h2 ⊢
  generalize cubeForm ω U (u - u') (u - u') = B₁ at h1 hBδle
  generalize cubeForm ω U u' u' = B₂ at h2 hBu'le
  generalize cubeEdgeNormSq U g = Ng at h1 hng ⊢
  generalize cubeEdgeNormSq U (g - g') = Ngg at h2 hngg ⊢
  generalize cubeEdgeNormSq U (q - q') = Nq at hBδle hnq ⊢
  generalize cubeEdgeNormSq U q' = Nq' at hBu'le hnq' ⊢
  have hsq : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h1' : a ^ 2 ≤ K * Ng * (2 * (2 * (K * Nq))) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK0 hng))
  have h2' : b ^ 2 ≤ K * Ngg * (2 * (2 * (K * Nq'))) :=
    h2.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK0 hngg))
  have e : 8 * K ^ 2 * (Ng * Nq + Ngg * Nq') =
      2 * (K * Ng * (2 * (2 * (K * Nq)))) + 2 * (K * Ngg * (2 * (2 * (K * Nq')))) := by ring
  rw [e]
  linarith

/-- A field bounded by `H` has squared edge norm at most `d |V| H²`. -/
theorem cubeEdgeNormSq_le (V : TriadicCube d) {h : Vertex d → Fin d → ℝ} {H : ℝ}
    (hh : ∀ x i, |h x i| ≤ H) : cubeEdgeNormSq V h ≤ d * V.latticeVolume * H ^ 2 := by
  have := sum_latticeEdge_sq_le V.toIntegerCube.vertices hh
  rw [V.card_toIntegerCube_vertices] at this
  unfold cubeEdgeNormSq
  linarith

theorem cubeEdgeNormSq_restrictField_le (V : TriadicCube d) (D : Finset (Vertex d))
    (h : Vertex d → Fin d → ℝ) : cubeEdgeNormSq V (cubeRestrictField D h) ≤ cubeEdgeNormSq V h := by
  unfold cubeEdgeNormSq
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · simp only [cubeRestrictField]
    split_ifs
    · exact le_rfl
    · rw [zero_pow two_ne_zero]
      exact sq_nonneg _
  · exact le_rfl

/-- The part of a field bounded by `H` on the edges of `V` not inside `D ⊆ V` has squared edge norm
at most `2d |V \ D| H²`. -/
theorem cubeEdgeNormSq_sub_restrictField_le (V : TriadicCube d) (D : Finset (Vertex d))
    {h : Vertex d → Fin d → ℝ} {H : ℝ} (hh : ∀ x i, |h x i| ≤ H) :
    cubeEdgeNormSq V (h - cubeRestrictField D h) ≤
      2 * d * ((V.toIntegerCube.vertices \ D).card : ℝ) * H ^ 2 := by
  set S := V.toIntegerCube.vertices with hS
  have hH2 : ∀ x i, h x i ^ 2 ≤ H ^ 2 := fun x i => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hh x i) 2
  have hpt : ∀ x ∈ S, ∀ i : Fin d,
      (if x + unit i ∈ S then (h - cubeRestrictField D h) x i ^ 2 else 0) ≤
        H ^ 2 * ((if x ∈ S \ D then (1 : ℝ) else 0) + if x + unit i ∈ S \ D then 1 else 0) := by
    intro x hx i
    have hR0 : 0 ≤ H ^ 2 * ((if x ∈ S \ D then (1 : ℝ) else 0) +
        if x + unit i ∈ S \ D then 1 else 0) := by
      have : 0 ≤ (if x ∈ S \ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have : 0 ≤ (if x + unit i ∈ S \ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      positivity
    by_cases h1 : x + unit i ∈ S
    · rw [if_pos h1]
      simp only [Pi.sub_apply, cubeRestrictField]
      by_cases hDD : x ∈ D ∧ x + unit i ∈ D
      · rw [if_pos hDD, sub_self, zero_pow two_ne_zero]
        exact hR0
      · rw [if_neg hDD, sub_zero]
        have hone : 1 ≤ (if x ∈ S \ D then (1 : ℝ) else 0) +
            if x + unit i ∈ S \ D then 1 else 0 := by
          by_cases hxD : x ∈ D
          · have hxiD : x + unit i ∉ D := fun h' => hDD ⟨hxD, h'⟩
            rw [if_pos (Finset.mem_sdiff.2 ⟨h1, hxiD⟩)]
            split_ifs <;> norm_num
          · rw [if_pos (Finset.mem_sdiff.2 ⟨hx, hxD⟩)]
            split_ifs <;> norm_num
        nlinarith [hH2 x i, sq_nonneg H]
    · rw [if_neg h1]
      exact hR0
  have hsum : ∑ x ∈ S, ∑ i : Fin d,
      (if x + unit i ∈ S then (h - cubeRestrictField D h) x i ^ 2 else 0) ≤
      H ^ 2 * (∑ x ∈ S, ∑ _i : Fin d, (if x ∈ S \ D then (1 : ℝ) else 0)) +
        H ^ 2 * (∑ x ∈ S, ∑ i : Fin d, if x + unit i ∈ S \ D then (1 : ℝ) else 0) := by
    calc _ ≤ ∑ x ∈ S, ∑ i : Fin d, H ^ 2 * ((if x ∈ S \ D then (1 : ℝ) else 0) +
          if x + unit i ∈ S \ D then 1 else 0) :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun i _ => hpt x hx i
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ x ∈ S, ∑ _i : Fin d, (if x ∈ S \ D then (1 : ℝ) else 0) =
      d * ((S \ D).card : ℝ) := by
    have e : ∀ x ∈ S, ∑ _i : Fin d, (if x ∈ S \ D then (1 : ℝ) else 0) =
        d * (if x ∈ S \ D then (1 : ℝ) else 0) := fun x _ => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hf : S.filter (fun x => x ∈ S \ D) = S \ D := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_boole, hf]
  have h2 : ∀ i : Fin d, ∑ x ∈ S, (if x + unit i ∈ S \ D then (1 : ℝ) else 0) ≤
      ((S \ D).card : ℝ) := by
    intro i
    rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_card_of_injOn (fun x => x + unit i)
      (fun x hx => (Finset.mem_filter.1 hx).2) (fun x _ y _ hxy => add_right_cancel hxy)
  have h3 : ∑ x ∈ S, ∑ i : Fin d, (if x + unit i ∈ S \ D then (1 : ℝ) else 0) ≤
      d * ((S \ D).card : ℝ) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _i : Fin d, ((S \ D).card : ℝ) := Finset.sum_le_sum fun i _ => h2 i
      _ = d * ((S \ D).card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cubeEdgeNormSq
  refine hsum.trans ?_
  rw [h1]
  have := sq_nonneg H
  nlinarith

/-- The pairing over the edges of `D ⊆ V` with the coarsened gradient is the field pairing with
the restricted field. -/
theorem latticeEdgePairing_eq_cubeFieldPairing_restrict {V : TriadicCube d}
    {D : Finset (Vertex d)} (hDV : D ⊆ V.toIntegerCube.vertices) (g : Vertex d → Fin d → ℝ)
    (w : CubeFun ω V) :
    latticeEdgePairing D g (fun x => cubeExtend ω V w (partitionAnchor ω x)) =
      cubeFieldPairing ω V (cubeRestrictField D g) w := by
  rw [cubeFieldPairing_apply, latticeEdgePairing]
  symm
  have hterm : ∀ x ∈ V.toIntegerCube.vertices, (∑ i : Fin d,
      if x + unit i ∈ V.toIntegerCube.vertices then
        cubeRestrictField D g x i * (cubeExtend ω V w (partitionAnchor ω (x + unit i)) -
          cubeExtend ω V w (partitionAnchor ω x)) else 0) =
      if x ∈ D then ∑ i : Fin d, (if x + unit i ∈ D then
        g x i * (cubeExtend ω V w (partitionAnchor ω (x + unit i)) -
          cubeExtend ω V w (partitionAnchor ω x)) else 0) else 0 := by
    intro x _
    by_cases hxD : x ∈ D
    · rw [if_pos hxD]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hxi : x + unit i ∈ D
      · rw [if_pos (hDV hxi), if_pos hxi, cubeRestrictField, if_pos ⟨hxD, hxi⟩]
      · rw [if_neg hxi, cubeRestrictField,
          if_neg (show ¬(x ∈ D ∧ x + unit i ∈ D) from fun h => hxi h.2)]
        split_ifs <;> ring
    · rw [if_neg hxD]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [cubeRestrictField, if_neg (show ¬(x ∈ D ∧ x + unit i ∈ D) from fun h => hxD h.1)]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.inter_eq_right.2 hDV]

theorem abs_le_sum_abs (q : Fin d → ℝ) (i : Fin d) : |q i| ≤ ∑ j, |q j| :=
  Finset.single_le_sum (f := fun j => |q j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- On a resolved cube, the partition cubes of the cluster have size at most `3^{scale V}`. -/
theorem three_pow_partitionCube_scale_le {V : TriadicCube d}
    {k : ℕ} (hk : ∀ x ∈ V.vertices, (partitionCube ω x).scale ≤ k) :
    ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ 3 ^ k := by
  intro z hz
  have hzV : z ∈ V.vertices := (V.mem_toIntegerCube_vertices z).1 (Finset.filter_subset _ _ hz)
  exact pow_le_pow_right₀ (by norm_num) (hk z hzV)

/-- **A deterministic bound for the subcube pairing**: `|X| ≤ 2d K² 3^{(2d-1)n} G Q`. -/
theorem abs_cubeSubcubePairing_le (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (ω : Configuration d) :
    |latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
          V.latticeVolume| ≤
      2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * G *
        ∑ i, |q i| := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 ⟨0, hd⟩)
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hv0 := V.latticeVolume_pos
  by_cases hω : PartitionEvent ω ∧ PartitionResolved ω V
  · obtain ⟨hP, hV⟩ := hω
    set K := coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) with hKdef
    have hK0 : 0 ≤ K := by positivity
    have hK : ∀ (h : Vertex d → Fin d → ℝ) (w : CubeFun ω V),
        cubeFieldPairing ω V h w ^ 2 ≤ K * cubeEdgeNormSq V h * (2 * cubeForm ω V w w) :=
      fun h w => cubeFieldPairing_sq_le_of_scale_le hd hP hV
        (three_pow_partitionCube_scale_le hV) h w
    obtain ⟨hu, hv⟩ := cubeMuMinimizer_spec hd hP hV q
    have hv' : ∀ w ∈ cubeHarmonic ω V, cubeForm ω V w (cubeMuMinimizer ω V q) =
        cubeFieldPairing ω V (fun _ => q) w := fun w hw => by
      rw [hv w hw, cubeCoarsePairing_eq_cubeFieldPairing_const, cubeFluxPairing_zero_slope,
        add_zero]
    have hB : cubeForm ω V (cubeMuMinimizer ω V q) (cubeMuMinimizer ω V q) ≤
        2 * (K * cubeEdgeNormSq V (fun _ => q)) :=
      le_two_mul_of_le_abs_of_sq_le (X := cubeFieldPairing ω V (fun _ => q) _)
        (cubeForm_self_nonneg _) (mul_nonneg hK0 (cubeEdgeNormSq_nonneg _ _))
        (by rw [← hv' _ hu]; exact le_abs_self _) (hK _ _)
    have hq := cubeEdgeNormSq_le V (h := fun _ => q) (H := Q) fun _ i => abs_le_sum_abs q i
    have hgN := cubeEdgeNormSq_le V hg
    have h1 := hK g (cubeMuMinimizer ω V q)
    rw [← cubeFieldPairing_eq_latticeEdgePairing, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
    rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]
    have hBn := cubeForm_self_nonneg (ω := ω) (cubeMuMinimizer ω V q)
    have hstep : K * cubeEdgeNormSq V g *
        (2 * cubeForm ω V (cubeMuMinimizer ω V q) (cubeMuMinimizer ω V q)) ≤
        K * (d * V.latticeVolume * G ^ 2) * (2 * (2 * (K * (d * V.latticeVolume * Q ^ 2)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hgN hK0) ?_ (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left hq hK0
      linarith
    refine h1.trans (hstep.trans (le_of_eq ?_))
    rw [hKdef]
    ring
  · have h0 : cubeMuMinimizer ω V q = 0 := by
      rw [cubeMuMinimizer, dif_neg fun h => hω ⟨h.2.1, h.2.2⟩]
    rw [h0]
    simp only [map_zero, Pi.zero_apply]
    have hz : latticeEdgePairing V.toIntegerCube.vertices g (fun _ => (0 : ℝ)) = 0 := by
      simp [latticeEdgePairing]
    rw [hz, zero_div, abs_zero]
    positivity

/-- **The pointwise comparison of display (5.31).** On the event that the partition agrees on `V`
with the partition capped at `k`, the subcube pairing and the localized pairing differ by at most
`(576 d³ K⁴ G² Q² 3^{(4d-1)k} / 3ⁿ)^{1/2}`. -/
theorem sq_sub_cubeSwitchLocValue_le (hd : 0 < d) {k : ℕ} {V : TriadicCube d}
    (hω : CubeCapGood k V ω) (hk : k + 2 < V.scale) (q : Fin d → ℝ)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) :
    (latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
          V.latticeVolume - cubeSwitchLocValue k V g q ω) ^ 2 ≤
      576 * d ^ 3 * coarseGradConstant d ^ 4 * G ^ 2 * (∑ i, |q i|) ^ 2 *
        ((3 : ℝ) ^ k) ^ (4 * d - 1) / 3 ^ V.scale := by
  have hP := hω.1
  have hV := hω.resolved (by omega)
  set D := switchInterior k V with hD
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 ⟨0, hd⟩)
  set K := coarseGradConstant d ^ 2 * ((3 : ℝ) ^ k) ^ (2 * d - 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ (h : Vertex d → Fin d → ℝ) (w : CubeFun ω V),
      cubeFieldPairing ω V h w ^ 2 ≤ K * cubeEdgeNormSq V h * (2 * cubeForm ω V w w) :=
    fun h w => cubeFieldPairing_sq_le_of_scale_le hd hP hV
      (three_pow_partitionCube_scale_le hω.scale_le) h w
  obtain ⟨hu, hv⟩ := cubeMuMinimizer_spec hd hP hV q
  have hv' : ∀ w ∈ cubeHarmonic ω V, cubeForm ω V w (cubeMuMinimizer ω V q) =
      cubeFieldPairing ω V (fun _ => q) w := fun w hw => by
    rw [hv w hw, cubeCoarsePairing_eq_cubeFieldPairing_const, cubeFluxPairing_zero_slope,
      add_zero]
  obtain ⟨ul, hul, hvl⟩ := exists_cubeMuGen_variation hd hP hV (cubeRestrictField D (fun _ => q)) 0
  have hvl' : ∀ w ∈ cubeHarmonic ω V, cubeForm ω V w ul =
      cubeFieldPairing ω V (cubeRestrictField D (fun _ => q)) w := fun w hw => by
    rw [hvl w hw, cubeFluxPairing_zero_slope, add_zero]
  have hv0 := V.latticeVolume_pos
  have hY : cubeSwitchLocValue k V g q ω =
      cubeFieldPairing ω V (cubeRestrictField D g) ul / V.latticeVolume := by
    unfold cubeSwitchLocValue
    rw [if_pos ⟨hP, hV⟩, cubeFieldPairing_eq_cubeMuGen hd hP hV hul hvl]
    field_simp
    rfl
  rw [← cubeFieldPairing_eq_latticeEdgePairing, hY, ← sub_div]
  have hcmp := sq_cubeFieldPairing_sub_le (g := g) (g' := cubeRestrictField D g)
    hu hul hv' hvl' hK0 hK
  have hqb : ∀ x i, |(fun _ : Vertex d => q) x i| ≤ Q := fun _ i => abs_le_sum_abs q i
  have h1 := cubeEdgeNormSq_le V hg
  have h2 := cubeEdgeNormSq_sub_restrictField_le V D hqb
  have h3 := cubeEdgeNormSq_sub_restrictField_le V D hg
  have h4 := (cubeEdgeNormSq_restrictField_le V D (fun _ => q)).trans (cubeEdgeNormSq_le V hqb)
  have hS : ((V.toIntegerCube.vertices \ D).card : ℝ) ≤
      2 * d * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ (k + 2) := card_sdiff_innerCube_le hk
  have hvol : V.latticeVolume = ((3 : ℝ) ^ V.scale) ^ d := rfl
  set s : ℝ := ((V.toIntegerCube.vertices \ D).card : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hb : cubeEdgeNormSq V g * cubeEdgeNormSq V ((fun _ => q) - cubeRestrictField D (fun _ => q)) +
      cubeEdgeNormSq V (g - cubeRestrictField D g) * cubeEdgeNormSq V (cubeRestrictField D (fun _ => q))
      ≤ 4 * d ^ 2 * V.latticeVolume * s * G ^ 2 * Q ^ 2 := by
    have e1 := mul_le_mul h1 h2 (cubeEdgeNormSq_nonneg _ _) (by positivity)
    have e2 := mul_le_mul h3 h4 (cubeEdgeNormSq_nonneg _ _) (by positivity)
    nlinarith
  have hc2 := hcmp.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  rw [div_pow, div_le_iff₀ (by positivity)]
  refine hc2.trans ?_
  -- the counting
  have hsv : s * ((3 : ℝ) ^ V.scale) ≤ 2 * d * V.latticeVolume * 3 ^ (k + 2) := by
    have hd1 : ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ V.scale = ((3 : ℝ) ^ V.scale) ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    calc s * 3 ^ V.scale ≤ 2 * d * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ (k + 2) * 3 ^ V.scale :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 2 * d * V.latticeVolume * 3 ^ (k + 2) := by rw [hvol, ← hd1]; ring
  have hKsq : K ^ 2 = coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1)) := by
    rw [hKdef, mul_pow, ← pow_mul]
    ring
  have hpow : ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1)) * 3 ^ (k + 2) = 9 * ((3 : ℝ) ^ k) ^ (4 * d - 1) := by
    rw [pow_add, show (3 : ℝ) ^ 2 = 9 by norm_num, show 4 * d - 1 = 2 * (2 * d - 1) + 1 by omega,
      pow_succ]
    ring
  have h3V : (0 : ℝ) < 3 ^ V.scale := by positivity
  rw [hKsq]
  have key : 8 * (coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1))) *
      (4 * d ^ 2 * V.latticeVolume * s * G ^ 2 * Q ^ 2) * 3 ^ V.scale ≤
      8 * (coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1))) *
      (4 * d ^ 2 * V.latticeVolume * G ^ 2 * Q ^ 2) * (2 * d * V.latticeVolume * 3 ^ (k + 2)) := by
    have hA : 0 ≤ 8 * (coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1))) *
        (4 * d ^ 2 * V.latticeVolume * G ^ 2 * Q ^ 2) := by positivity
    calc _ = 8 * (coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1))) *
          (4 * d ^ 2 * V.latticeVolume * G ^ 2 * Q ^ 2) * (s * 3 ^ V.scale) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsv hA
  rw [← le_div_iff₀ h3V] at key
  refine key.trans (le_of_eq ?_)
  have e : 8 * (coarseGradConstant d ^ 4 * ((3 : ℝ) ^ k) ^ (2 * (2 * d - 1))) *
      (4 * d ^ 2 * V.latticeVolume * G ^ 2 * Q ^ 2) * (2 * d * V.latticeVolume * 3 ^ (k + 2)) =
      64 * d ^ 3 * coarseGradConstant d ^ 4 * G ^ 2 * Q ^ 2 * V.latticeVolume ^ 2 *
        (((3 : ℝ) ^ k) ^ (2 * (2 * d - 1)) * 3 ^ (k + 2)) := by ring
  rw [e, hpow]
  field_simp
  ring

end Rigidity.Percolation
