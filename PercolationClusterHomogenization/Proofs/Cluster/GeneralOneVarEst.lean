import PercolationClusterHomogenization.Proofs.Cluster.GeneralRestrictField
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubcubeCrossing
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessNuExpect

/-!
# Display (5.30) of Armstrong and Dario in every dimension

Steps 1–3 of the proof of Lemma 5.7 of Armstrong and Dario, up to display (5.30), in every dimension
`d ≥ 2`. Let `g` be the solenoidal field of scale `n` in the direction `e_k`
(`cubeSolenoidalField`: equal to `e_k` near `□_n`, bounded by `10`, divergence free, vanishing off
the edges of `□_{n+1}`), and let `V` run over the `3^d` subcubes of scale `n` of `□_{n+1}`.

* The pairing of `g` with the gradient of any function over the edges of `□_{n+1}` vanishes
  (`latticeEdgePairing_cubeSolenoidalField_eq_zero`, display (5.28)).
* Hence `∑_V ⟨∇[u(·, V, q)]_𝒫, g⟩_V` is minus the sum of the crossing term of Step 2 and of the
  differences `⟨∇[u(·, □_{n+1}, q)]_𝒫 - ∇[u(·, V, q)]_𝒫, g⟩_V` of Lemma 5.5
  (`ofReal_sum_subcube_cubeSolenoidal_sq_le`).
* With Step 2 (`exists_lintegral_latticeEdgePairing_sub_sum_subcubesAt_le` with `a = 4d`) and
  Lemma 5.5 for the pairings with a bounded field (`exists_lintegral_cubeMuRestrictFieldError_le`
  with `m = n + 1`):
  `E[|∑_V |□_n|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V|²] ≤ C |q|² (τ_n + 3^{-n/4})`
  (`exists_lintegral_sum_subcube_cubeSolenoidal_sq_le`, display (5.30)), for `n ≥ 2d`.

The differences of the coarsened minimizers of `μ` across the edges of the cube are measurable
functions of the configuration (`measurable_cubeMuMinimizer_edge`, by polarization through
`μ_{g,p}`), hence so are the pairings with fixed fields. The two-dimensional version is
`Rigidity.Proofs.Cluster.exists_lintegral_sum_subcube_solenoidal_sq_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The coarse pairing of `μ` is the field pairing of the constant field. -/
theorem cubeCoarsePairing_eq_cubeFieldPairing_const {ω : Configuration d} (U : TriadicCube d)
    (q : Fin d → ℝ) (u : CubeFun ω U) :
    cubeCoarsePairing ω U q u = cubeFieldPairing ω U (fun _ => q) u + cubeFluxPairing ω U 0 u := by
  rw [cubeFluxPairing_zero_slope, add_zero, cubeFieldPairing_apply,
    cubeCoarsePairing_eq_latticeEdgePairing]
  rfl

/-- **Measurability of the coarsened minimizers of `μ` across an edge.** For `x` and `x + eᵢ` in
`V`, the difference `[u(·, V, q)]_𝒫(x + eᵢ) - [u(·, V, q)]_𝒫(x)` is a measurable function of the
configuration: it is the pairing of `u(·, V, q)` with the field supported on that edge, given by
polarization through `μ_{g,p}` on the event that the partition exists and resolves `V`, and zero
off this event. -/
theorem measurable_cubeMuMinimizer_edge (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ)
    {x : Vertex d} {i : Fin d} (hx : x ∈ V.toIntegerCube.vertices)
    (hxi : x + unit i ∈ V.toIntegerCube.vertices) :
    Measurable fun ω : Configuration d =>
      cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω (x + unit i)) -
        cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x) := by
  set g : Vertex d → Fin d → ℝ := fun y k => if y = x ∧ k = i then 1 else 0 with hg
  set g' : Vertex d → Fin d → ℝ := fun _ => q with hg'
  have hpair : ∀ (ω : Configuration d) (u : CubeFun ω V), cubeFieldPairing ω V g u =
      cubeExtend ω V u (partitionAnchor ω (x + unit i)) -
        cubeExtend ω V u (partitionAnchor ω x) := by
    intro ω u
    rw [cubeFieldPairing_apply, Finset.sum_eq_single_of_mem x hx,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [hg, hxi]
    all_goals intro b _ hb; simp [hg, hb]
  have hpol : ∀ ω : Configuration d, cubeFieldPairing ω V g (cubeMuMinimizer ω V q) =
      -V.latticeVolume *
        ((if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V (g + g') 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g' 0 else 0)) := by
    intro ω
    by_cases hω : PartitionEvent ω ∧ PartitionResolved ω V
    · rw [if_pos hω, if_pos hω, if_pos hω]
      obtain ⟨hu, hfv⟩ := cubeMuMinimizer_spec hd hω.1 hω.2 q
      exact cubeFieldPairing_eq_cubeMuGen hd hω.1 hω.2 hu
        (fun w hw => by rw [hfv w hw, cubeCoarsePairing_eq_cubeFieldPairing_const]) g
    · rw [if_neg hω, if_neg hω, if_neg hω]
      have h0 : cubeMuMinimizer ω V q = 0 := by
        rw [cubeMuMinimizer, dif_neg fun h => hω ⟨h.2.1, h.2.2⟩]
      rw [h0, map_zero]
      ring
  have hfun : (fun ω : Configuration d =>
      cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω (x + unit i)) -
        cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) = fun ω =>
      -V.latticeVolume *
        ((if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V (g + g') 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g 0 else 0) -
          (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMuGen ω V g' 0 else 0)) := by
    funext ω
    rw [← hpair, hpol]
  rw [hfun]
  exact (((measurable_cubeMuGen_indicator V (g + g') 0).sub
    (measurable_cubeMuGen_indicator V g 0)).sub (measurable_cubeMuGen_indicator V g' 0)).const_mul _

/-- The pairing of a fixed field over a subset `D` of `U` with the coarsened gradient of the
minimizer of `μ(U, q)` is a measurable function of the configuration. -/
theorem aemeasurable_latticeEdgePairing_cubeMuMinimizer (hd : 0 < d) {p : unitInterval}
    {U : TriadicCube d} {D : Finset (Vertex d)} (hDU : D ⊆ U.toIntegerCube.vertices)
    (g : Vertex d → Fin d → ℝ) (q : Fin d → ℝ) :
    AEMeasurable (fun ω => latticeEdgePairing D g
      (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)))
      (latticeBondLaw d p) :=
  aemeasurable_latticeEdgePairing_of_edge D g fun _ hx _ hxi =>
    (measurable_cubeMuMinimizer_edge hd U q (hDU hx) (hDU hxi)).aemeasurable

/-- The algebra of the pointwise bound of display (5.30): for `N` terms with `A = -∑ S`,
`((∑ T)/c)² ≤ 2 c⁻² A² + 2 N² (N⁻¹ ∑ ((S - T)/c)²)`. -/
theorem sq_sum_div_le_of_neg_sum {ι : Type*} {s : Finset ι} (S T : ι → ℝ) {A : ℝ}
    (hA : A = -∑ i ∈ s, S i) {c : ℝ} (hc : 0 < c) :
    ((∑ i ∈ s, T i) / c) ^ 2 ≤
      2 / c ^ 2 * A ^ 2 + 2 * (s.card : ℝ) ^ 2 *
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, ((S i - T i) / c) ^ 2) := by
  have hCS := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => S i - T i)
  have hsumT : ∑ i ∈ s, T i = -A - ∑ i ∈ s, (S i - T i) := by
    rw [hA, Finset.sum_sub_distrib]
    ring
  have hsq : ∑ i ∈ s, ((S i - T i) / c) ^ 2 = (∑ i ∈ s, (S i - T i) ^ 2) / c ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
  rw [hsq, hsumT]
  set B := ∑ i ∈ s, (S i - T i)
  set D := ∑ i ∈ s, (S i - T i) ^ 2
  have hB : B ^ 2 ≤ s.card * D := hCS
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := by positivity
  have e1 : 2 * (s.card : ℝ) ^ 2 * ((s.card : ℝ)⁻¹ * (D / c ^ 2)) = 2 * s.card * D / c ^ 2 := by
    rcases (Nat.cast_nonneg (α := ℝ) s.card).lt_or_eq with h | h
    · field_simp
    · rw [← h]
      simp
  rw [e1, div_pow, div_le_iff₀ hc2]
  have e2 : (2 / c ^ 2 * A ^ 2 + 2 * s.card * D / c ^ 2) * c ^ 2 = 2 * A ^ 2 + 2 * s.card * D := by
    field_simp
  rw [e2]
  nlinarith [sq_nonneg (A - B)]

/-- **The pointwise bound of display (5.30).** The square of the normalized sum of the subcube
pairings with the solenoidal field is at most `2 · 3^{-2dn}` times the square of the crossing term
plus `2 · 3^{2d}` times the quantity of Lemma 5.5 with the field. -/
theorem ofReal_sum_subcube_cubeSolenoidal_sq_le (ω : Configuration d) {n : ℕ} (hn : 2 ≤ n)
    (q : Fin d → ℝ) {k l : Fin d} (hkl : k ≠ l) :
    ENNReal.ofReal ((∑ V ∈ (⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n,
        latticeEdgePairing V.toIntegerCube.vertices (cubeSolenoidalField n k l)
          (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
            ((3 : ℝ) ^ n) ^ d) ^ 2) ≤
      ENNReal.ofReal (2 / (((3 : ℝ) ^ n) ^ d) ^ 2) *
        ENNReal.ofReal ((latticeEdgePairing (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices
            (cubeSolenoidalField n k l) (fun x => cubeExtend ω (⟨n + 1, 0⟩ : TriadicCube d)
              (cubeMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube d) q) (partitionAnchor ω x)) -
          ∑ V ∈ (⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n,
            latticeEdgePairing V.toIntegerCube.vertices (cubeSolenoidalField n k l)
              (fun x => cubeExtend ω (⟨n + 1, 0⟩ : TriadicCube d)
                (cubeMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube d) q) (partitionAnchor ω x))) ^ 2) +
        ENNReal.ofReal (2 * (((⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n).card : ℝ) ^ 2) *
          ENNReal.ofReal (cubeMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube d) n q
            (cubeSolenoidalField n k l)) := by
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  set g := cubeSolenoidalField n k l with hgdef
  set fU : Vertex d → ℝ := fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)
    with hfU
  have hsol := latticeEdgePairing_cubeSolenoidalField_eq_zero hn hkl fU
  have hc : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hreal := sq_sum_div_le_of_neg_sum (s := U.subcubesAt n)
    (fun V => latticeEdgePairing V.toIntegerCube.vertices g fU)
    (fun V => latticeEdgePairing V.toIntegerCube.vertices g
      (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)))
    (A := latticeEdgePairing U.toIntegerCube.vertices g fU -
      ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g fU)
    (by rw [hsol, zero_sub]) hc
  have hfe : ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n,
      ((latticeEdgePairing V.toIntegerCube.vertices g fU -
        latticeEdgePairing V.toIntegerCube.vertices g
          (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x))) /
            ((3 : ℝ) ^ n) ^ d) ^ 2 =
      cubeMuRestrictFieldError ω U n q g := by
    rw [cubeMuRestrictFieldError, cubeRestrictFieldError]
    congr 1
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [TriadicCube.latticeVolume, TriadicCube.scale_of_mem_subcubesAt hV]
  rw [hfe] at hreal
  have hfe0 : 0 ≤ cubeMuRestrictFieldError ω U n q g := cubeRestrictFieldError_nonneg _ _ _ _ _
  rw [← Finset.sum_div]
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]

/-- The arithmetic of the crossing term: `2 N² 3^{-n} |□_{n+1}|^{1/(4d)} ≤ 2 · 3^{2d+1} 3^{-n/4}`,
`N = 3^d`. -/
theorem crossing_arith_general (hd : 0 < d) (n : ℕ) :
    2 / (((3 : ℝ) ^ n) ^ d) ^ 2 * (((3 : ℝ) ^ (n + 1)) ^ d / 3 ^ n) * ((3 : ℝ) ^ (n + 1)) ^ d *
        (((3 : ℝ) ^ (n + 1)) ^ d) ^ (1 / ((4 * d : ℕ) : ℝ)) ≤
      2 * 3 ^ (2 * d + 1) * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  have hpow : (((3 : ℝ) ^ (n + 1)) ^ d) ^ (1 / ((4 * d : ℕ) : ℝ)) =
      (3 : ℝ) ^ (((n : ℝ) + 1) / 4) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  have hV : ((3 : ℝ) ^ (n + 1)) ^ d = 3 ^ d * ((3 : ℝ) ^ n) ^ d := by
    rw [pow_succ, mul_pow, mul_comm]
  rw [hpow, hV]
  have hVp : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have e1 : 2 / (((3 : ℝ) ^ n) ^ d) ^ 2 * (3 ^ d * ((3 : ℝ) ^ n) ^ d / 3 ^ n) *
      (3 ^ d * ((3 : ℝ) ^ n) ^ d) = 2 * 3 ^ (2 * d) / 3 ^ n := by
    rw [show (3 : ℝ) ^ (2 * d) = 3 ^ d * 3 ^ d by rw [two_mul, pow_add]]
    field_simp
  rw [e1]
  have h1 : (3 : ℝ) ^ (((n : ℝ) + 1) / 4) / 3 ^ n = (3 : ℝ) ^ (((n : ℝ) + 1) / 4 - n) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
  have h2 : 3 * (3 : ℝ) ^ (-(n : ℝ) / 4) = (3 : ℝ) ^ (1 + -(n : ℝ) / 4) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have h3 : (3 : ℝ) ^ (((n : ℝ) + 1) / 4 - n) ≤ (3 : ℝ) ^ (1 + -(n : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  calc 2 * 3 ^ (2 * d) / 3 ^ n * (3 : ℝ) ^ (((n : ℝ) + 1) / 4)
      = 2 * 3 ^ (2 * d) * ((3 : ℝ) ^ (((n : ℝ) + 1) / 4) / 3 ^ n) := by ring
    _ ≤ 2 * 3 ^ (2 * d) * (3 * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * 3 ^ (2 * d + 1) * (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [pow_succ]; ring

/-- **Display (5.30) of Armstrong and Dario** (proof of Lemma 5.7, Step 3, every dimension
`d ≥ 2`, `p > p_c(d)`): for `n ≥ 2d` and the solenoidal field `g` of scale `n` in a coordinate
direction, `E[|∑_V |□_n|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V|²] ≤ C |q|² (τ_n + 3^{-n/4})`, the sum running
over the subcubes `V` of scale `n` of `□_{n+1}`. -/
theorem exists_lintegral_sum_subcube_cubeSolenoidal_sq_le [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 * d ≤ n → ∀ (q : Fin d → ℝ) (k l : Fin d), k ≠ l →
      ∫⁻ ω, ENNReal.ofReal ((∑ V ∈ (⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n,
          latticeEdgePairing V.toIntegerCube.vertices (cubeSolenoidalField n k l)
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
              ((3 : ℝ) ^ n) ^ d) ^ 2) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * (cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₁, hC₁, hfield⟩ := exists_lintegral_cubeMuRestrictFieldError_le hd hpc
  obtain ⟨C₂, hC₂, hcross⟩ := exists_lintegral_latticeEdgePairing_sub_sum_subcubesAt_le hd hpc
    (a := 4 * d) (by omega)
  set N : ℝ := (3 : ℝ) ^ d with hNdef
  refine ⟨100 * (2 * C₂ * (2 * 3 ^ (2 * d + 1)) + 2 * N ^ 2 * C₁), by positivity,
    fun n hn q k l hkl => ?_⟩
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  have hUs : U.scale = n + 1 := rfl
  have hnU : n ≤ U.scale := by omega
  set g := cubeSolenoidalField n k l with hgdef
  have hg : ∀ x i, |g x i| ≤ 10 := abs_cubeSolenoidalField_le n k l
  set P := ∑ i, q i ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  set μ := latticeBondLaw d p with hμ
  have hcard : ((U.subcubesAt n).card : ℝ) = N := by
    have h := card_subcubesAt_mul_general U hnU
    rw [TriadicCube.latticeVolume, hUs, pow_succ, mul_pow] at h
    have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
    rw [hNdef]
    field_simp at h
    linarith
  -- the crossing term
  set Xc : Configuration d → ℝ := fun ω => (latticeEdgePairing U.toIntegerCube.vertices g
      (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) -
    ∑ V ∈ U.subcubesAt n, latticeEdgePairing V.toIntegerCube.vertices g
      (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x))) ^ 2 with hXc
  have hXcm : AEMeasurable Xc μ := by
    refine ((aemeasurable_latticeEdgePairing_cubeMuMinimizer hd0 subset_rfl g q).sub
      (Finset.aemeasurable_fun_sum _ fun V hV =>
        aemeasurable_latticeEdgePairing_cubeMuMinimizer hd0 ?_ g q)).pow_const 2
    intro x hx
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx ⊢
    exact TriadicCube.subset_of_mem_subcubesAt hnU hV hx
  have hcb := hcross U n hnU q g 10 hg
  have hfb := hfield n (n + 1) q g 10 hg hn (by omega) (by omega)
  rw [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add] at hfb
  refine (lintegral_mono fun ω => ofReal_sum_subcube_cubeSolenoidal_sq_le ω (by omega) q hkl).trans
    ?_
  rw [lintegral_add_left' ((hXcm.ennreal_ofReal).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (add_le_add (mul_le_mul_of_nonneg_left hcb zero_le)
    (mul_le_mul_of_nonneg_left hfb zero_le)).trans ?_
  have hvol0 := U.latticeVolume_pos
  have hτn := cubeTau_nonneg (d := d) p n
  rw [hcard, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add
      (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (by positivity) hP0) (by positivity)) hvol0.le) (by positivity)))
      (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hC₁ (mul_nonneg (by positivity) hP0))
        (add_nonneg hτn (by positivity))))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hvU : U.latticeVolume = ((3 : ℝ) ^ (n + 1)) ^ d := by rw [TriadicCube.latticeVolume, hUs]
  rw [hvU, ← three_rpow_neg_div_four_eq]
  set x := (3 : ℝ) ^ (-(n : ℝ) / 4) with hx
  set τ := cubeTau (d := d) p n with hτ
  have hτ0 : 0 ≤ τ := cubeTau_nonneg p n
  have hx0 : 0 ≤ x := by positivity
  have harith := crossing_arith_general hd0 n
  set y := 2 / (((3 : ℝ) ^ n) ^ d) ^ 2 * (((3 : ℝ) ^ (n + 1)) ^ d / 3 ^ n) *
    ((3 : ℝ) ^ (n + 1)) ^ d * (((3 : ℝ) ^ (n + 1)) ^ d) ^ (1 / ((4 * d : ℕ) : ℝ)) with hy
  have e1 : 2 / (((3 : ℝ) ^ n) ^ d) ^ 2 * (C₂ * 10 ^ 2 * P * (((3 : ℝ) ^ (n + 1)) ^ d / 3 ^ n) *
      ((3 : ℝ) ^ (n + 1)) ^ d * (((3 : ℝ) ^ (n + 1)) ^ d) ^ (1 / ((4 * d : ℕ) : ℝ))) =
      C₂ * 100 * P * y := by
    rw [hy]
    ring
  rw [e1]
  have hy' : C₂ * 100 * P * y ≤ C₂ * 100 * P * (2 * 3 ^ (2 * d + 1) * x) :=
    mul_le_mul_of_nonneg_left harith (by positivity)
  have h2 : 2 * N ^ 2 * (C₁ * (10 ^ 2 * P) * (τ + x)) =
      100 * (2 * N ^ 2 * C₁) * P * (τ + x) := by ring
  rw [h2]
  have h3 : C₂ * 100 * P * (2 * 3 ^ (2 * d + 1) * x) ≤
      100 * (2 * C₂ * (2 * 3 ^ (2 * d + 1))) * P * (τ + x) := by
    have : x ≤ τ + x := by linarith
    calc C₂ * 100 * P * (2 * 3 ^ (2 * d + 1) * x)
        = 100 * (C₂ * (2 * 3 ^ (2 * d + 1))) * P * x := by ring
      _ ≤ 100 * (C₂ * (2 * 3 ^ (2 * d + 1))) * P * (τ + x) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 100 * (2 * C₂ * (2 * 3 ^ (2 * d + 1))) * P * (τ + x) := by
          gcongr
          linarith
  nlinarith

end Rigidity.Percolation
