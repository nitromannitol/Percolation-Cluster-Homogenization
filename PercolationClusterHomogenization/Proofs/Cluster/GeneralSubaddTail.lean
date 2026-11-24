import PercolationClusterHomogenization.Proofs.Cluster.GeneralSIUpgrade

/-!
# Deterministic bounds on the event of small partition cubes for Proposition 5.2, in every
dimension

On the event `PartitionSizeLe ω U ℓ`, with `w = 3^ℓ` and `L = 3^{scale U}`:

* the partition sizes on the faces of `U` sum to at most `2d w L^{d-1}`
  (`faceSizeSum_le_of_sizeLe`), and those near the faces, weighted as in the lower bound of `ν`,
  to at most `w^{2(d-1)} d e 2 L^{d-1} (w + 1)` (`marginSizeSum_le_of_sizeLe`), by the exponential
  sums over the margins;
* hence the error `Y(U)` of the comparison of `μ` and `ν` is at most `Yc(ℓ) L^{-1/2}`
  (`cubeComparisonError_le_of_sizeLe`), and the bound `Λ(U)` of `-μ(U, ·)` is at most
  `d² K² w^{2(d-1)}` (`cubeMuBound_le_of_sizeLe`).

These are the inputs of Lemma 5.3 (`cube_minimalset`) in the proof of Proposition 5.2 of Armstrong
and Dario from Lemma 5.11, as in the two-dimensional
`Rigidity.Proofs.Cluster.planarSubaddGood_of_event`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

theorem faceSizeSum_le_of_sizeLe {U : TriadicCube d} {ℓ : ℕ} (hS : PartitionSizeLe ω U ℓ) :
    faceSizeSum ω U ≤ 2 * d * (3 : ℝ) ^ ℓ * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
  have hsize : (U.toIntegerCube.size : ℝ) = (3 : ℝ) ^ U.scale := U.cast_size_toIntegerCube
  have hface : ∀ (F : Finset (Vertex d)), F ⊆ U.toIntegerCube.vertices →
      F.card ≤ U.toIntegerCube.size ^ (d - 1) →
      ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ≤
        (3 : ℝ) ^ ℓ * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
    intro F hF hcard
    calc ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x
        ≤ ∑ _x ∈ F, (3 : ℝ) ^ ℓ := Finset.sum_le_sum fun x hx => hS.stoppingSize_le (hF hx)
      _ = (F.card : ℝ) * (3 : ℝ) ^ ℓ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((U.toIntegerCube.size ^ (d - 1) : ℕ) : ℝ) * (3 : ℝ) ^ ℓ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = (3 : ℝ) ^ ℓ * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
          push_cast
          rw [hsize]
          ring
  unfold faceSizeSum
  calc ∑ i : Fin d, (∑ x ∈ U.toIntegerCube.upperFace i,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
      ∑ x ∈ U.toIntegerCube.lowerFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)
      ≤ ∑ _i : Fin d, 2 * ((3 : ℝ) ^ ℓ * ((3 : ℝ) ^ U.scale) ^ (d - 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := hface (U.toIntegerCube.upperFace i) (Finset.filter_subset _ _)
          (U.toIntegerCube.card_upperFace_le i)
        have h2 := hface (U.toIntegerCube.lowerFace i) (Finset.filter_subset _ _)
          (U.toIntegerCube.card_lowerFace_le i)
        linarith
    _ = 2 * d * (3 : ℝ) ^ ℓ * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem marginSizeSum_le_of_sizeLe {U : TriadicCube d} {ℓ : ℕ} (hS : PartitionSizeLe ω U ℓ) :
    marginSizeSum ω U ≤ ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) *
      (d * (Real.exp 1 * (2 * ((3 : ℝ) ^ U.scale) ^ (d - 1) * ((3 : ℝ) ^ ℓ + 1)))) := by
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw0 : 0 < w := by positivity
  have hpt : ∀ z ∈ U.toIntegerCube.vertices, ∀ i : Fin d,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
        (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
          then 1 else 0) ≤
      w ^ (2 * (d - 1)) * (Real.exp 1 * Real.exp (-(U.margin z i : ℝ) / w)) := by
    intro z hz i
    have hs := hS.stoppingSize_le hz
    have hs0 := stoppingSize_nonneg (TriadicCube.goodCubes ω) z
    have hpow : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) ≤
        w ^ (2 * (d - 1)) := pow_le_pow_left₀ hs0 hs _
    have hind : (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
        then (1 : ℝ) else 0) ≤ if (U.margin z i : ℝ) < w then (1 : ℝ) else 0 := by
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h1.trans_le hs) h2
      · norm_num
      · exact le_rfl
    have h3 := ite_lt_le_exp_mul_exp_neg_div (m := (U.margin z i : ℝ)) hw0
    have hi0 : (0 : ℝ) ≤ if (U.margin z i : ℝ) < TriadicCube.stoppingSize
        (TriadicCube.goodCubes ω) z then 1 else 0 := by split_ifs <;> norm_num
    calc TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
          (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
            then 1 else 0)
        ≤ w ^ (2 * (d - 1)) * (if (U.margin z i : ℝ) < w then (1 : ℝ) else 0) :=
          mul_le_mul hpow hind hi0 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  unfold marginSizeSum
  calc ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
          (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
            then 1 else 0)
      ≤ ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          w ^ (2 * (d - 1)) * (Real.exp 1 * Real.exp (-(U.margin z i : ℝ) / w)) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun i _ => hpt z hz i
    _ = w ^ (2 * (d - 1)) * ∑ i : Fin d, Real.exp 1 *
          ∑ z ∈ U.toIntegerCube.vertices, Real.exp (-(U.margin z i : ℝ) / w) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ w ^ (2 * (d - 1)) * ∑ _i : Fin d, Real.exp 1 *
          (2 * ((3 : ℝ) ^ U.scale) ^ (d - 1) * (w + 1)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact (sum_exp_neg_margin_le U i hw0).trans (mul_le_mul_of_nonneg_left
          (inv_one_sub_exp_neg_inv_le hw0) (by positivity))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The constant of the bound of the comparison error on the event of small partition cubes. -/
noncomputable def comparisonCap (d : ℕ) (ℓ : ℕ) : ℝ :=
  1 + 2 * d * (3 : ℝ) ^ ℓ + 2 * 3 ^ d * √(d * (((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) *
    (d * (Real.exp 1 * (2 * ((3 : ℝ) ^ ℓ + 1))))))

theorem comparisonCap_nonneg (d ℓ : ℕ) : 0 ≤ comparisonCap d ℓ := by
  unfold comparisonCap
  positivity

/-- **The comparison error on the event of small partition cubes**:
`Y(U) ≤ Yc(ℓ) 3^{-scale U / 2}`. -/
theorem cubeComparisonError_le_of_sizeLe (hd : 0 < d) {U : TriadicCube d} {ℓ : ℕ}
    (hS : PartitionSizeLe ω U ℓ) :
    cubeComparisonError ω U ≤ comparisonCap d ℓ * (1 / √((3 : ℝ) ^ U.scale)) := by
  set L : ℝ := (3 : ℝ) ^ U.scale with hL
  have hL1 : 1 ≤ L := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by positivity
  set t : ℝ := √L with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hL0
  have htt : t ^ 2 = L := Real.sq_sqrt hL0.le
  have ht1 : 1 ≤ t := Real.one_le_sqrt.2 hL1
  have hV : U.latticeVolume = L ^ d := rfl
  have hLd : L ^ d = L ^ (d - 1) * L := by rw [← pow_succ, Nat.sub_add_cancel hd]
  have hLdm : 0 < L ^ (d - 1) := by positivity
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw0 : 0 ≤ w := by positivity
  set Z : ℝ := d * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1))))) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hF := faceSizeSum_le_of_sizeLe hS
  have hM := marginSizeSum_le_of_sizeLe hS
  rw [← hL, ← hw] at hF hM
  have hF' : faceSizeSum ω U / U.latticeVolume ≤ 2 * d * w * (1 / t) := by
    rw [hV, div_le_iff₀ (by positivity)]
    have : 2 * d * w * (1 / t) * L ^ d = 2 * d * w * L ^ (d - 1) * (L / t) := by
      rw [hLd]
      ring
    rw [this]
    have hLt : 1 ≤ L / t := by
      rw [le_div_iff₀ ht0, one_mul, ← htt]
      nlinarith
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Nat.cast_nonneg d)) hw0) hLdm.le]
  have hM' : d * marginSizeSum ω U / U.latticeVolume ≤ Z / L := by
    rw [hV, div_le_div_iff₀ (by positivity) hL0, hLd]
    have h := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg d)
    have e : (d : ℝ) * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * L ^ (d - 1) * (w + 1))))) =
        Z * L ^ (d - 1) := by
      rw [hZ]
      ring
    rw [e] at h
    nlinarith [hL0]
  have hsq : √(d * marginSizeSum ω U / U.latticeVolume) ≤ √Z * (1 / t) := by
    calc √(d * marginSizeSum ω U / U.latticeVolume) ≤ √(Z / L) := Real.sqrt_le_sqrt hM'
      _ = √Z * (1 / t) := by rw [Real.sqrt_div' _ hL0.le, ht, div_eq_mul_one_div]
  have h1L : 1 / L ≤ 1 / t := by
    rw [div_le_div_iff₀ hL0 ht0, one_mul, one_mul, ← htt]
    nlinarith
  unfold cubeComparisonError
  rw [← hL]
  have e : comparisonCap d ℓ * (1 / t) = 1 * (1 / t) + 2 * d * w * (1 / t) +
      2 * 3 ^ d * (√Z * (1 / t)) := by
    rw [comparisonCap, ← hw, ← hZ]
    ring
  rw [e]
  have k := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * 3 ^ d)
  linarith

/-- **The bound of `-μ` on the event of small partition cubes**. -/
theorem cubeMuBound_le_of_sizeLe {U V : TriadicCube d} {ℓ : ℕ} (hS : PartitionSizeLe ω U ℓ)
    (hVU : V.vertices ⊆ U.vertices) :
    cubeMuBound ω V ≤ d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) := by
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

/-- The good event of Proposition 5.2 at a triadic cube `V`, with constant `K` and rate `λ`: the
partition exists and resolves `V`, and `|μ(V, q) + (1/2) q · ā⁻¹ q|` and
`|ν(V, ā⁻¹ q) - (1/2) q · ā⁻¹ q|` are at most `K |q|² λ^{scale V}` for every `q`. -/
def CubeSubaddGood (p : unitInterval) (ω : Configuration d) (V : TriadicCube d) (K lam : ℝ) :
    Prop :=
  PartitionEvent ω ∧ PartitionResolved ω V ∧
    (∀ q : Fin d → ℝ, |cubeMu ω V q + 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i| ≤
      K * (∑ i, q i ^ 2) * lam ^ V.scale) ∧
    ∀ q : Fin d → ℝ,
      |cubeNu ω V ((cubeAhom p)⁻¹ *ᵥ q) - 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i| ≤
        K * (∑ i, q i ^ 2) * lam ^ V.scale

/-- **Lemma 5.3 on the event of small partition cubes**: if the partition cubes of `U` have scale
at most `ℓ ≤ scale U` and `ρ(U) ≤ T`, then `U` is in the good event of Proposition 5.2 with the
bound `B = ρ-part + Y-part` computed from `T`, `Yc(ℓ) 3^{-scale U/2}` and `d² K² 3^{2ℓ(d-1)}`. -/
theorem cubeSubaddGood_of_sizeLe (hd : 0 < d) (p : unitInterval) {U : TriadicCube d} {ℓ : ℕ}
    (hSL : PartitionSizeLe ω U ℓ) (hℓU : ℓ ≤ U.scale) {S : ℝ} (hS0 : 0 ≤ S)
    (hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) {T B lam : ℝ}
    (hρ : cubeRho p ω U ≤ T)
    (hB : T + d * (comparisonCap d ℓ * (1 / √((3 : ℝ) ^ U.scale))) * S +
      d / 2 * (2 * d * (comparisonCap d ℓ * (1 / √((3 : ℝ) ^ U.scale))) * S +
        √(4 * d * (d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) + 1) *
          (T + comparisonCap d ℓ * (1 / √((3 : ℝ) ^ U.scale)) * S))) ≤ B * lam ^ U.scale) :
    CubeSubaddGood p ω U B lam := by
  have hU : PartitionResolved ω U := hSL.resolved subset_rfl hℓU
  have hY := cubeComparisonError_le_of_sizeLe hd hSL
  have hY0 := cubeComparisonError_nonneg ω U
  have hΛ := cubeMuBound_le_of_sizeLe hSL (subset_rfl : U.vertices ⊆ U.vertices)
  have hΛ0 := cubeMuBound_nonneg ω U
  have hρ0 := cubeRho_nonneg hd p ω U
  set Yb : ℝ := comparisonCap d ℓ * (1 / √((3 : ℝ) ^ U.scale)) with hYb
  set Λb : ℝ := d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) with hΛb
  have hsq : √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S)) ≤
      √(4 * d * (Λb + 1) * (T + Yb * S)) := by
    refine Real.sqrt_le_sqrt ?_
    have h1 : cubeRho p ω U + cubeComparisonError ω U * S ≤ T + Yb * S :=
      add_le_add hρ (mul_le_mul_of_nonneg_right hY hS0)
    have h2 : 0 ≤ cubeRho p ω U + cubeComparisonError ω U * S := by positivity
    have h3 : 4 * d * (cubeMuBound ω U + 1) ≤ 4 * d * (Λb + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact mul_le_mul h3 h1 h2 (by positivity)
  have hYS : cubeComparisonError ω U * S ≤ Yb * S := mul_le_mul_of_nonneg_right hY hS0
  have hμb : d / 2 * (2 * d * cubeComparisonError ω U * S +
      √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S))) ≤
      B * lam ^ U.scale := by
    have k : d / 2 * (2 * d * cubeComparisonError ω U * S +
        √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S))) ≤
        d / 2 * (2 * d * Yb * S + √(4 * d * (Λb + 1) * (T + Yb * S))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : 2 * d * cubeComparisonError ω U * S ≤ 2 * d * Yb * S := by
        have := mul_le_mul_of_nonneg_left hYS (by positivity : (0 : ℝ) ≤ 2 * d)
        linarith
      linarith
    have hT0 : 0 ≤ T := hρ0.trans hρ
    have hYb0 : 0 ≤ Yb := hY0.trans hY
    have : 0 ≤ T + d * Yb * S := by positivity
    linarith
  have hνb : cubeRho p ω U + d * cubeComparisonError ω U * S +
      d / 2 * (2 * d * cubeComparisonError ω U * S +
        √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S))) ≤
      B * lam ^ U.scale := by
    have k1 : d * cubeComparisonError ω U * S ≤ d * Yb * S := by
      have := mul_le_mul_of_nonneg_left hYS (Nat.cast_nonneg d)
      linarith
    have k2 : 2 * d * cubeComparisonError ω U * S ≤ 2 * d * Yb * S := by
      have := mul_le_mul_of_nonneg_left hYS (by positivity : (0 : ℝ) ≤ 2 * d)
      linarith
    have k3 := mul_le_mul_of_nonneg_left (add_le_add k2 hsq) (by positivity : (0 : ℝ) ≤ d / 2)
    linarith
  refine ⟨hSL.1, hU, fun q => ?_, fun q => ?_⟩
  · have h := (cube_minimalset hd p hSL.1 hU hS0 hSb q).1
    have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
    calc _ ≤ _ := h
      _ ≤ B * lam ^ U.scale * ∑ i, q i ^ 2 := mul_le_mul_of_nonneg_right hμb hq0
      _ = B * (∑ i, q i ^ 2) * lam ^ U.scale := by ring
  · have h := (cube_minimalset hd p hSL.1 hU hS0 hSb q).2
    have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
    calc _ ≤ _ := h
      _ ≤ B * lam ^ U.scale * ∑ i, q i ^ 2 := mul_le_mul_of_nonneg_right hνb hq0
      _ = B * (∑ i, q i ^ 2) * lam ^ U.scale := by ring

end Rigidity.Percolation
