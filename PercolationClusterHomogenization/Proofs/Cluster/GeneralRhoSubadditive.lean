import PercolationClusterHomogenization.Proofs.Cluster.GeneralSIStepTwo

/-!
# Deterministic bounds on the event of small partition cubes, in every dimension

On the event `PartitionSizeLe ω U ℓ` (the partition exists and the partition cubes of the vertices
of `U` have scale at most `ℓ`), for `ℓ ≤ n ≤ scale U`:

* `U` and its subcubes of scale `n` are resolved;
* a vertex `x` of `U` is exceptional at scale `n` (`ExceptionalMajorant`) only within distance
  `3^{ℓ+1}` of a face of its subcube, so that, by the exponential sums over the margins
  (`sum_exp_neg_margin_le`), there are at most `2d e (3^{ℓ+1} + 1) |U| 3^{-n}` of them
  (`card_filter_exceptionalMajorant_le`);
* `ρ(V) ≤ C₁(ℓ)` for every triadic cube `V ⊆ U` of scale at least `ℓ`, from `ν ≤ (3ᵈ/4) |ξ|₁²`
  and the bound of `-μ` by the partition sizes (`cubeRho_le_of_sizeLe`), the bound `ρ ≤ C₁` of
  Step 1 of the proof of Lemma 5.11 of Armstrong and Dario.

These are the general-dimensional forms of the bounds of `Rigidity.Proofs.Cluster` on the event
`PlanarReachLe` that the planar reach is small.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The partition exists and the partition cubes of the vertices of `U` have scale at most `ℓ`. -/
def PartitionSizeLe (ω : Configuration d) (U : TriadicCube d) (ℓ : ℕ) : Prop :=
  PartitionEvent ω ∧ ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ ℓ

theorem PartitionSizeLe.resolved {U V : TriadicCube d} {ℓ : ℕ} (h : PartitionSizeLe ω U ℓ)
    (hV : V.vertices ⊆ U.vertices) (hℓ : ℓ ≤ V.scale) : PartitionResolved ω V :=
  fun x hx => (h.2 x (hV hx)).trans hℓ

theorem PartitionSizeLe.stoppingSize_le {U : TriadicCube d} {ℓ : ℕ} (h : PartitionSizeLe ω U ℓ)
    {x : Vertex d} (hx : x ∈ U.toIntegerCube.vertices) :
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ≤ (3 : ℝ) ^ ℓ := by
  rw [stoppingSize_goodCubes_eq h.1 x]
  exact pow_le_pow_right₀ (by norm_num) (h.2 x ((U.mem_toIntegerCube_vertices x).1 hx))

/-- `1{m < M} ≤ e · exp(-m/M)`. -/
theorem ite_lt_le_exp_mul_exp_neg_div {m M : ℝ} (hM : 0 < M) :
    (if m < M then (1 : ℝ) else 0) ≤ Real.exp 1 * Real.exp (-m / M) := by
  split_ifs with h
  · rw [← Real.exp_add]
    refine Real.one_le_exp ?_
    have : m / M < 1 := (div_lt_one hM).2 h
    rw [neg_div]
    linarith
  · positivity

/-- `(1 - exp(-1/M))⁻¹ ≤ M + 1`. -/
theorem inv_one_sub_exp_neg_inv_le {M : ℝ} (hM : 0 < M) :
    (1 - Real.exp (-1 / M))⁻¹ ≤ M + 1 := by
  have h1 : 1 + 1 / M ≤ Real.exp (1 / M) := by
    have := Real.add_one_le_exp (1 / M)
    linarith
  have h2 : Real.exp (-1 / M) ≤ M / (M + 1) := by
    rw [neg_div, Real.exp_neg]
    calc (Real.exp (1 / M))⁻¹ ≤ (1 + 1 / M)⁻¹ := inv_anti₀ (by positivity) h1
      _ = M / (M + 1) := by rw [one_add_div hM.ne', inv_div, add_comm]
  have h3 : 1 / (M + 1) ≤ 1 - Real.exp (-1 / M) := by
    have e : 1 - M / (M + 1) = 1 / (M + 1) := by field_simp; ring
    linarith
  have h4 : 0 < 1 / (M + 1) := by positivity
  calc (1 - Real.exp (-1 / M))⁻¹ ≤ (1 / (M + 1))⁻¹ := inv_anti₀ h4 h3
    _ = M + 1 := by rw [one_div, inv_inv]

/-- **The exceptional vertices on the event of small partition cubes**: at most
`2d e (3^{ℓ+1} + 1) |U| 3^{-n}` vertices of `U` are exceptional at scale `n`. -/
theorem card_filter_exceptionalMajorant_le (hd : 0 < d) {U : TriadicCube d} {ℓ n : ℕ}
    (hS : PartitionSizeLe ω U ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ U.scale) :
    ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) ≤
      2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) * U.latticeVolume / (3 : ℝ) ^ n := by
  set M : ℝ := (3 : ℝ) ^ (ℓ + 1) with hM
  have hM0 : 0 < M := by positivity
  have hpt : ∀ x ∈ U.toIntegerCube.vertices, (if ExceptionalMajorant ω n x then (1 : ℝ) else 0) ≤
      ∑ i : Fin d, Real.exp 1 * Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / M) := by
    intro x hx
    split_ifs with hex
    · have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
      have hsub := triadicCubeAt_subset hn hxU
      rcases hex with ⟨z, hz, hzs⟩ | ⟨i, hi⟩
      · exfalso
        have hzU : z ∈ U.toIntegerCube.vertices := (U.mem_toIntegerCube_vertices z).2
          (hsub (((triadicCubeAt n x).mem_toIntegerCube_vertices z).1 hz))
        have h1 := hS.stoppingSize_le hzU
        have h2 : (3 : ℝ) ^ ℓ ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hℓn
        linarith
      · have hsz := hS.stoppingSize_le hx
        have hi' : ((triadicCubeAt n x).margin x i : ℝ) < M := by
          rw [hM, pow_succ]
          linarith
        have h1 := ite_lt_le_exp_mul_exp_neg_div (m := ((triadicCubeAt n x).margin x i : ℝ)) hM0
        rw [if_pos hi'] at h1
        exact h1.trans (Finset.single_le_sum (f := fun i : Fin d => Real.exp 1 *
          Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / M)) (fun j _ => by positivity)
          (Finset.mem_univ i))
    · positivity
  have hcard : ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) =
      ∑ x ∈ U.toIntegerCube.vertices, (if ExceptionalMajorant ω n x then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [sum_triadicCubeAt_eq hn (fun V x => ∑ i : Fin d, Real.exp 1 *
    Real.exp (-(V.margin x i : ℝ) / M))]
  have hV : ∀ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin d,
      Real.exp 1 * Real.exp (-(V.margin x i : ℝ) / M) ≤
      d * (Real.exp 1 * (2 * ((3 : ℝ) ^ n) ^ (d - 1) * (M + 1))) := by
    intro V hVm
    rw [Finset.sum_comm]
    calc ∑ i : Fin d, ∑ x ∈ V.toIntegerCube.vertices,
          Real.exp 1 * Real.exp (-(V.margin x i : ℝ) / M)
        ≤ ∑ _i : Fin d, Real.exp 1 * (2 * ((3 : ℝ) ^ n) ^ (d - 1) * (M + 1)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          have h := sum_exp_neg_margin_le V i hM0
          rw [TriadicCube.scale_of_mem_subcubesAt hVm] at h
          refine h.trans (mul_le_mul_of_nonneg_left (inv_one_sub_exp_neg_inv_le hM0)
            (by positivity))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hV).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := card_subcubesAt_mul_general U hn
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hd' : ((3 : ℝ) ^ n) ^ d = ((3 : ℝ) ^ n) ^ (d - 1) * (3 : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hd'] at hc
  rw [le_div_iff₀ h3n, ← hc]
  ring_nf
  exact le_rfl

/-- `|ā⁻¹ q|₁² ≤ S² d |q|²` for an `ℓ¹` operator bound `S` of `ā⁻¹`. -/
theorem sq_sum_abs_mulVec_le {p : unitInterval} {S : ℝ}
    (hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) (q : Fin d → ℝ) :
    (∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ q) i|) ^ 2 ≤ S ^ 2 * d * ∑ i, q i ^ 2 := by
  have h1 := hSb q
  have h2 := sq_sum_abs_le_card_mul q
  have h3 : (0 : ℝ) ≤ ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ q) i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  calc (∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ q) i|) ^ 2 ≤ (S * ∑ i, |q i|) ^ 2 :=
        pow_le_pow_left₀ h3 h1 2
    _ = S ^ 2 * (∑ i, |q i|) ^ 2 := by ring
    _ ≤ S ^ 2 * (d * ∑ i, q i ^ 2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = S ^ 2 * d * ∑ i, q i ^ 2 := by ring

/-- **`ρ ≤ C₁(ℓ)` on the event of small partition cubes** (Step 1 of the proof of Lemma 5.11 of
Armstrong and Dario): for a triadic cube `V ⊆ U` of scale at least `ℓ`,
`ρ(V) ≤ (3ᵈ/4) S² d + d² K² 3^{2ℓ(d-1)}`, `K` the constant of Lemma 3.3. -/
theorem cubeRho_le_of_sizeLe [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {U V : TriadicCube d} {ℓ : ℕ}
    (hS : PartitionSizeLe ω U ℓ) (hVU : V.vertices ⊆ U.vertices) (hℓ : ℓ ≤ V.scale) {S : ℝ}
    (hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) :
    cubeRho p ω V ≤ 3 ^ d / 4 * S ^ 2 * d +
      d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
  have hd0 : 0 < d := by omega
  have hres := hS.resolved hVU hℓ
  have hMB : cubeMuBound ω V ≤
      d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
    unfold cubeMuBound
    have hvol := V.latticeVolume_pos
    have hsum : ∑ z ∈ V.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) ≤
        V.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
      calc ∑ z ∈ V.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))
          ≤ ∑ _z ∈ V.toIntegerCube.vertices, ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
            refine Finset.sum_le_sum fun z hz => pow_le_pow_left₀ (stoppingSize_nonneg _ _) ?_ _
            exact hS.stoppingSize_le ((U.mem_toIntegerCube_vertices z).2
              (hVU ((V.mem_toIntegerCube_vertices z).1 hz)))
        _ = V.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul, V.card_toIntegerCube_vertices]
    rw [div_le_iff₀ hvol]
    have hK : 0 ≤ (d : ℝ) * d * coarseGradConstant d ^ 2 := by positivity
    calc (d : ℝ) * d * coarseGradConstant d ^ 2 * ∑ z ∈ V.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))
        ≤ d * d * coarseGradConstant d ^ 2 * (V.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1))) :=
          mul_le_mul_of_nonneg_left hsum hK
      _ = _ := by ring
  refine cubeRho_le_of_forall (by positivity) fun q => ?_
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  refine max_le ?_ (by positivity)
  have hν := cubeNu_le (ω := ω) (U := V) ((cubeAhom (d := d) p)⁻¹ *ᵥ q)
  have hξ := sq_sum_abs_mulVec_le hSb q
  have hμ := neg_cubeMu_le_cubeMuBound_mul hd0 hS.1 hres q
  have hdot := sum_mul_inv_cubeAhom_mulVec_nonneg hd hpc q
  have hμ' := mul_le_mul_of_nonneg_right hMB hq0
  have hν' := mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 3 ^ d / 4)
  simp only [cubeOmega, if_pos (And.intro hS.1 hres)]
  linarith

/-- The error constant of the subadditivity of `ρ` on the event of small partition cubes. -/
noncomputable def rhoSubaddConst (d : ℕ) (S : ℝ) (ℓ : ℕ) : ℝ :=
  d * (muSubaddConst d * (((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) + ((3 : ℝ) ^ ℓ) ^ (2 * d) *
      (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1))) / 2 +
    3 ^ d / 4 * S ^ 2 * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) + 1))

theorem rhoSubaddConst_nonneg (d : ℕ) {S : ℝ} (ℓ : ℕ) : 0 ≤ rhoSubaddConst d S ℓ := by
  have := muSubaddConst_nonneg d
  unfold rhoSubaddConst
  positivity

/-- The error of the subadditivity of `μ` in the proof of (5.56), with `t = 1/s`. -/
theorem subadd_err_mu_le {m Q₁ D A B vol a b κ N s : ℝ} (hm : 0 ≤ m) (hQ₁ : Q₁ ≤ D)
    (hQ₁0 : 0 ≤ Q₁) (hs : 0 < s) (hA : A ≤ vol * a) (hA0 : 0 ≤ A) (hB : B ≤ b * N)
    (hB0 : 0 ≤ B) (hb : 0 ≤ b) (hN : N ≤ κ * vol / s ^ 2) :
    m * Q₁ * (1 / s * A + B / (1 / s)) / 2 ≤ m * D * (vol * (1 / s) * (a + b * κ)) / 2 := by
  have h1 : 1 / s * A + B / (1 / s) ≤ vol * (1 / s) * (a + b * κ) := by
    have e1 : B / (1 / s) = B * s := by rw [div_div_eq_mul_div, div_one]
    have k1 : 1 / s * A ≤ 1 / s * (vol * a) := mul_le_mul_of_nonneg_left hA (by positivity)
    have k2 : B * s ≤ b * (κ * vol / s ^ 2) * s :=
      mul_le_mul_of_nonneg_right (hB.trans (mul_le_mul_of_nonneg_left hN hb)) hs.le
    have e2 : b * (κ * vol / s ^ 2) * s = vol * (1 / s) * (b * κ) := by
      field_simp
    rw [e1]
    have e3 : vol * (1 / s) * (a + b * κ) = 1 / s * (vol * a) + vol * (1 / s) * (b * κ) := by
      ring
    rw [e3]
    linarith
  have h2 : 0 ≤ 1 / s * A + B / (1 / s) := by positivity
  have h3 := mul_le_mul hQ₁ h1 h2 (hQ₁0.trans hQ₁)
  have h4 := mul_le_mul_of_nonneg_left h3 hm
  have e : m * D * (vol * (1 / s) * (a + b * κ)) / 2 =
      m * (D * (vol * (1 / s) * (a + b * κ))) / 2 := by ring
  rw [e, mul_assoc]
  exact div_le_div_of_nonneg_right h4 (by norm_num)

/-- The error of the subadditivity of `ν` in the proof of (5.56). -/
theorem subadd_err_nu_le {c Ξ₁ E G vol κ N s : ℝ} (hc : 0 ≤ c) (hΞ : Ξ₁ ≤ E) (hΞ0 : 0 ≤ Ξ₁)
    (hs : 0 < s) (hG : G ≤ N) (hG0 : 0 ≤ G) (hvol : 0 ≤ vol) (hN : N ≤ κ * vol / s ^ 2) :
    c * Ξ₁ * (s * G + vol / s) ≤ c * E * (vol * (1 / s) * (κ + 1)) := by
  have h1 : s * G + vol / s ≤ vol * (1 / s) * (κ + 1) := by
    have k1 : s * G ≤ s * (κ * vol / s ^ 2) := mul_le_mul_of_nonneg_left (hG.trans hN) hs.le
    have e1 : s * (κ * vol / s ^ 2) = vol * (1 / s) * κ := by field_simp
    have e2 : vol / s = vol * (1 / s) := by rw [mul_one_div]
    have e3 : vol * (1 / s) * (κ + 1) = vol * (1 / s) * κ + vol * (1 / s) := by ring
    rw [e2, e3]
    linarith
  have h2 : 0 ≤ s * G + vol / s := by positivity
  have h3 := mul_le_mul hΞ h1 h2 (hΞ0.trans hΞ)
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  calc c * Ξ₁ * (s * G + vol / s) = c * (Ξ₁ * (s * G + vol / s)) := by ring
    _ ≤ c * (E * (vol * (1 / s) * (κ + 1))) := h4
    _ = c * E * (vol * (1 / s) * (κ + 1)) := by ring

/-- On the event of small partition cubes, the exceptional vertices of the cluster in the sense of
the subadditivity of `ν` are exceptional in the sense of `ExceptionalMajorant`. -/
theorem subcubeExceptionalCount_le (hP : PartitionEvent ω) (U : TriadicCube d) (n : ℕ) :
    subcubeExceptionalCount ω U n ≤
      ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) := by
  have hsub : (crossingClusterVertices ω U).filter (IsSubcubeExceptional ω n) ⊆
      U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨(U.mem_toIntegerCube_vertices x).2
      (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 hx.1)),
      exceptionalMajorant_of_isSubcubeExceptional hP hx.2⟩
  unfold subcubeExceptionalCount
  exact_mod_cast Finset.card_le_card hsub

/-- The sum of `ρ` over the vertices of `U`, each counted in its subcube of scale `n`. -/
theorem sum_cubeRho_triadicCubeAt_eq (p : unitInterval) {U : TriadicCube d} {n : ℕ}
    (hn : n ≤ U.scale) :
    ∑ x ∈ U.toIntegerCube.vertices, cubeRho p ω (triadicCubeAt n x) =
      ((3 : ℝ) ^ n) ^ d * ∑ V ∈ U.subcubesAt n, cubeRho p ω V := by
  rw [sum_triadicCubeAt_eq hn (fun V _ => cubeRho p ω V), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.sum_const, nsmul_eq_mul, V.card_toIntegerCube_vertices]
  change ((3 : ℝ) ^ V.scale) ^ d * _ = _
  rw [TriadicCube.scale_of_mem_subcubesAt hV]

/-- **The subadditivity of `ρ` on the event of small partition cubes** (display (5.56) of the
proof of Lemma 5.11 of Armstrong and Dario, with the errors of (4.32) and (4.33)): for
`ℓ ≤ n ≤ scale U`, `ρ(U) ≤ |𝒮|⁻¹ ∑_{V ∈ 𝒮} ρ(V) + C(ℓ) 3^{-n/2}`, `𝒮` the subcubes of scale `n`
of `U`. -/
theorem cubeRho_le_avg_add_of_sizeLe [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    {U : TriadicCube d} {ℓ n : ℕ}
    (hS : PartitionSizeLe ω U ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ U.scale) {S : ℝ}
    (hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) :
    cubeRho p ω U ≤ ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, cubeRho p ω V +
      rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)) := by
  have hd0 : 0 < d := by omega
  have hP := hS.1
  have hU : PartitionResolved ω U := hS.resolved subset_rfl (hℓn.trans hn)
  have hVres : ∀ x ∈ U.toIntegerCube.vertices, PartitionResolved ω (triadicCubeAt n x) :=
    fun x hx => hS.resolved (triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x).1 hx))
      (by rw [scale_triadicCubeAt]; exact hℓn)
  have hL0 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hs0 : 0 < √((3 : ℝ) ^ n) := Real.sqrt_pos.2 hL0
  have hss : √((3 : ℝ) ^ n) ^ 2 = (3 : ℝ) ^ n := Real.sq_sqrt hL0.le
  have hvol0 : 0 < U.latticeVolume := U.latticeVolume_pos
  have hNb := card_filter_exceptionalMajorant_le hd0 hS hℓn hn
  rw [← hss] at hNb
  have hpow : ∀ z ∈ U.toIntegerCube.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ 3 ^ ℓ :=
    fun z hz => by
      rw [← stoppingSize_goodCubes_eq hP z]
      exact hS.stoppingSize_le hz
  have hA : ∑ z ∈ U.toIntegerCube.vertices,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) ≤
      U.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
    calc _ ≤ ∑ _z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) :=
          Finset.sum_le_sum fun z hz => pow_le_pow_left₀ (by positivity) (hpow z hz) _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, U.card_toIntegerCube_vertices]
  have hB : ∑ z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
      (if ExceptionalMajorant ω n z then 1 else 0) ≤
      ((3 : ℝ) ^ ℓ) ^ (2 * d) *
        ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) := by
    calc _ ≤ ∑ z ∈ U.toIntegerCube.vertices,
          ((3 : ℝ) ^ ℓ) ^ (2 * d) * (if ExceptionalMajorant ω n z then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (hpow z hz) _) (by split_ifs <;> norm_num)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.card_filter]
          push_cast
          rfl
  have hB0 : 0 ≤ ∑ z ∈ U.toIntegerCube.vertices,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
        (if ExceptionalMajorant ω n z then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  have hA0 : 0 ≤ ∑ z ∈ U.toIntegerCube.vertices,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) :=
    Finset.sum_nonneg fun z _ => by positivity
  have hG := subcubeExceptionalCount_le hP U n
  have hG0 : 0 ≤ subcubeExceptionalCount ω U n := Nat.cast_nonneg _
  have hcard : ((U.subcubesAt n).card : ℝ) * ((3 : ℝ) ^ n) ^ d = U.latticeVolume :=
    card_subcubesAt_mul_general U hn
  have hc0 : ((U.subcubesAt n).card : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    exact hvol0.ne' hcard.symm
  have hvolR : U.latticeVolume * (((U.subcubesAt n).card : ℝ)⁻¹ *
      ∑ V ∈ U.subcubesAt n, cubeRho p ω V) =
      ((3 : ℝ) ^ n) ^ d * ∑ V ∈ U.subcubesAt n, cubeRho p ω V := by
    rw [← hcard]
    field_simp
  have hR0 : 0 ≤ ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, cubeRho p ω V :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun V _ => cubeRho_nonneg hd0 p ω V)
  have hmu0 := muSubaddConst_nonneg d
  have hC0 := rhoSubaddConst_nonneg d (S := S) ℓ
  have ht0 : 0 ≤ 1 / √((3 : ℝ) ^ n) := by positivity
  refine cubeRho_le_of_forall (add_nonneg hR0 (mul_nonneg hC0 ht0)) fun q => ?_
  have hQ0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hμ := sum_cubeMu_subcubes_sub_le hd0 hP hU hn q (by positivity : 0 < 1 / √((3 : ℝ) ^ n))
  rw [Finset.sum_congr rfl fun x hx => if_pos (hVres x hx)] at hμ
  have hν := cubeNu_mul_latticeVolume_le_sum_add hd0 hP hn ((cubeAhom (d := d) p)⁻¹ *ᵥ q) hs0
  have hEμ := subadd_err_mu_le hmu0 (sq_sum_abs_le_card_mul q) (sq_nonneg _) hs0 hA hA0 hB hB0
    (by positivity) hNb
  have hEν := subadd_err_nu_le (by positivity : (0 : ℝ) ≤ 3 ^ d / 4)
    (sq_sum_abs_mulVec_le hSb q) (sq_nonneg _) hs0 hG hG0 hvol0.le hNb
  have hωU : cubeOmega p ω U q = cubeNu ω U ((cubeAhom (d := d) p)⁻¹ *ᵥ q) + -cubeMu ω U q -
      ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i := by
    simp only [cubeOmega, if_pos (And.intro hP hU)]
  have hωV : ∀ x ∈ U.toIntegerCube.vertices, cubeOmega p ω (triadicCubeAt n x) q =
      cubeNu ω (triadicCubeAt n x) ((cubeAhom (d := d) p)⁻¹ *ᵥ q) +
        -cubeMu ω (triadicCubeAt n x) q - ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i :=
    fun x hx => by simp only [cubeOmega, if_pos (And.intro hP (hVres x hx))]
  have hsumω : ∑ x ∈ U.toIntegerCube.vertices, cubeOmega p ω (triadicCubeAt n x) q ≤
      (∑ i, q i ^ 2) * ∑ x ∈ U.toIntegerCube.vertices, cubeRho p ω (triadicCubeAt n x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ =>
      (cubeOmega_le_cubeRho_mul hd0 p ω _ q).trans_eq (mul_comm _ _)
  rw [Finset.sum_congr rfl hωV, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, U.card_toIntegerCube_vertices,
    sum_cubeRho_triadicCubeAt_eq p hn, ← hvolR] at hsumω
  have hCdef : rhoSubaddConst d S ℓ = d * (muSubaddConst d * (((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) +
      ((3 : ℝ) ^ ℓ) ^ (2 * d) * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1))) / 2 +
      3 ^ d / 4 * S ^ 2 * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) + 1)) := rfl
  have key : U.latticeVolume * cubeOmega p ω U q ≤ U.latticeVolume *
      ((((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, cubeRho p ω V +
        rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n))) * ∑ i, q i ^ 2) := by
    rw [hωU, hCdef]
    linarith
  exact max_le (le_of_mul_le_mul_left key hvol0) (by positivity)

end Rigidity.Percolation
