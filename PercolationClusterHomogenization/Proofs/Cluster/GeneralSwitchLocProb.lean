import PercolationClusterHomogenization.Proofs.Cluster.GeneralSwitchLocCompare
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReachConcentrationHolds

/-!
# Display (5.31) of Armstrong and Dario in every dimension

The partition agrees on a triadic cube `V` of scale `n` with the partition capped at scale `k`
outside an event of probability at most `C (2 · 3^{n-k} + 29)^d exp(-c 3^k)`
(`exists_measure_not_cubeCapGood_le`, Proposition 4.9 with the cap at `k`). With `k = ⌊n/(8d)⌋`,
the pointwise comparison on this event and the deterministic bound off it give, for `n ≥ 8d`,
`E[(X - Y)²] ≤ C G² |q|₁² 3^{-n/4}` (`exists_lintegral_sq_sub_cubeSwitchLoc_le`), where
`X = |V|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V` and `Y` is the local version, which is measurable for the
bonds inside `V`. This is display (5.31) of Armstrong and Dario (the localization of the proof of
Lemma 5.7, by the second variation rather than by Lemma 4.11). The two-dimensional version is
`Rigidity.Proofs.Cluster.exists_lintegral_sq_sub_switchLoc_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Localization of the partition at the cap `k`** (Armstrong and Dario, Proposition 4.9, every
dimension `d ≥ 2`). -/
theorem exists_measure_not_cubeCapGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube d) (k : ℕ),
      ∃ S : Set (Configuration d), MeasurableSet S ∧
        (∀ ω, ω ∉ S → CubeCapGood k V ω) ∧
        latticeBondLaw d p S ≤ ENNReal.ofReal (C * (2 * 3 ^ (V.scale - k) + 29) ^ d *
          Real.exp (-c * (3 : ℝ) ^ k)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_measure_ne_cappedCube_goodCubes_le hd hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun V k => ?_⟩
  set S₀ := {ω : Configuration d | ∃ x ∈ V.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
    Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
      Q ≠ TriadicCube.cappedCube (TriadicCube.goodCubes ω) k x} with hS₀
  set S₁ := {ω : Configuration d | ¬ PartitionEvent ω} with hS₁
  refine ⟨toMeasurable (latticeBondLaw d p) (S₁ ∪ S₀), measurableSet_toMeasurable _ _,
    fun ω hω => ?_, ?_⟩
  · have hω' : ω ∉ S₁ ∪ S₀ := fun h => hω (subset_toMeasurable _ _ h)
    simp only [Set.mem_union, not_or, hS₁, hS₀, Set.mem_setOf_eq, not_not] at hω'
    refine ⟨hω'.1, fun x hx => ?_⟩
    by_contra hne
    exact hω'.2 ⟨x, hx, _, (partitionCube_spec hω'.1 x).1, (partitionCube_spec hω'.1 x).2, hne⟩
  · rw [measure_toMeasurable]
    have h0 : latticeBondLaw d p S₁ = 0 := ae_iff.1 (ae_partitionEvent hd hpc)
    refine (measure_union_le _ _).trans ?_
    rw [h0, zero_add]
    refine (h V k).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal hC,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    ring

/-- Clamping to `[-M, M]` does not increase the distance to a point of `[-M, M]`. -/
theorem abs_sub_max_min_le {X Y M : ℝ} (hX : |X| ≤ M) : |X - max (-M) (min M Y)| ≤ |X - Y| := by
  obtain ⟨h1, h2⟩ := abs_le.1 hX
  rcases le_total Y M with hYM | hYM
  · rw [min_eq_right hYM]
    rcases le_total (-M) Y with hY | hY
    · rw [max_eq_right hY]
    · rw [max_eq_left hY, abs_of_nonneg (by linarith : 0 ≤ X - -M),
        abs_of_nonneg (by linarith : 0 ≤ X - Y)]
      linarith
  · rw [min_eq_left hYM, max_eq_right (by linarith : -M ≤ M),
      abs_of_nonpos (by linarith : X - M ≤ 0), abs_of_nonpos (by linarith : X - Y ≤ 0)]
    linarith

theorem inv_three_pow_le_three_rpow (n : ℕ) :
    ((3 : ℝ) ^ n)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem three_pow_cap_div_le {n k : ℕ} (h : 8 * d * k ≤ n) :
    ((3 : ℝ) ^ k) ^ (4 * d - 1) / 3 ^ n ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h1 : k * (4 * d - 1) ≤ 4 * d * k := by
    rw [mul_comm]
    exact Nat.mul_le_mul_right k (Nat.sub_le _ _)
  have h' : ((k * (4 * d - 1) : ℕ) : ℝ) ≤ 4 * d * k := by exact_mod_cast h1
  have h'' : (8 : ℝ) * d * k ≤ n := by exact_mod_cast h
  linarith

/-- **Display (5.31) of Armstrong and Dario** (every dimension `d ≥ 2`, `p > p_c(d)`). For
`n ≥ 8d` and `k = ⌊n/(8d)⌋`, the subcube pairing and its local version differ in mean square by at
most `C G² |q|₁² 3^{-n/4}`. -/
theorem exists_lintegral_sq_sub_cubeSwitchLoc_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : TriadicCube d, 8 * d ≤ V.scale → ∀ (q : Fin d → ℝ)
      (g : Vertex d → Fin d → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∫⁻ ω, ENNReal.ofReal ((latticeEdgePairing V.toIntegerCube.vertices g
          (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
            V.latticeVolume -
          cubeSwitchLoc (V.scale / (8 * d)) V g q
            (2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * G *
              ∑ i, |q i|) ω) ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * G ^ 2 * (∑ i, |q i|) ^ 2 * (3 : ℝ) ^ (-(V.scale : ℝ) / 4)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Cp, hCp, c, hc, hS⟩ := exists_measure_not_cubeCapGood_le hd hpc
  set B : ℕ := 40 * d ^ 2 with hB
  obtain ⟨KB, hKB, hKBk⟩ := exists_exp_neg_rpow_le_inv_pow hc one_pos B
  set K₄ := coarseGradConstant d ^ 4 with hK₄
  set C₁ : ℝ := 576 * d ^ 3 * K₄ with hC₁
  set C₂ : ℝ := 16 * d ^ 2 * K₄ * Cp * 31 ^ d * KB * 3 ^ B with hC₂
  refine ⟨C₁ + C₂, by positivity, fun V hn q g G hg => ?_⟩
  set n := V.scale with hndef
  set k := n / (8 * d) with hkdef
  set Q := ∑ i, |q i| with hQdef
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 ⟨0, hd0⟩)
  set M := 2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ n) ^ (2 * d - 1) * G * Q with hMdef
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨S, hSm, hSgood, hSμ⟩ := hS V k
  have hk1 : 1 ≤ k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h8 : 8 * d * k ≤ n := Nat.mul_div_le n (8 * d)
  have hnk : n < 8 * d * (k + 1) := by
    have := Nat.lt_mul_div_succ n (show 0 < 8 * d by omega)
    rw [hkdef]
    linarith
  have hk2 : k + 2 < n := by
    have : 16 * k ≤ 8 * d * k := Nat.mul_le_mul_right k (by omega)
    omega
  set b₁ := 576 * d ^ 3 * coarseGradConstant d ^ 4 * G ^ 2 * Q ^ 2 *
    ((3 : ℝ) ^ k) ^ (4 * d - 1) / 3 ^ n with hb₁
  have hpt : ∀ ω, ENNReal.ofReal ((latticeEdgePairing V.toIntegerCube.vertices g
      (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
        V.latticeVolume - cubeSwitchLoc k V g q M ω) ^ 2) ≤
      ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) * S.indicator 1 ω := by
    intro ω
    have hXM := abs_cubeSubcubePairing_le hd0 V q hg ω
    have hYM := abs_cubeSwitchLoc_le (k := k) (V := V) g q hM0 ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      rw [← sq_abs]
      calc |_| ^ 2 ≤ (M + M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
            ((abs_sub _ _).trans (add_le_add hXM hYM)) 2
        _ = 4 * M ^ 2 := by ring
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hgood := hSgood ω hω
      refine ENNReal.ofReal_le_ofReal ?_
      rw [cubeSwitchLoc_eq_of_cubeCapGood hgood hk2 g q M]
      have hcl := abs_sub_max_min_le (Y := cubeSwitchLocValue k V g q ω) hXM
      have hcmp := sq_sub_cubeSwitchLocValue_le hd0 hgood hk2 q hg
      calc _ ≤ (latticeEdgePairing V.toIntegerCube.vertices g
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
              V.latticeVolume - cubeSwitchLocValue k V g q ω) ^ 2 := by
            rw [← sq_abs, ← sq_abs (_ - cubeSwitchLocValue k V g q ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
        _ ≤ b₁ := hcmp
  have hint : ∫⁻ ω, (ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) * S.indicator 1 ω)
      ∂(latticeBondLaw d p) = ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) *
        latticeBondLaw d p S := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (measurable_one.indicator hSm), lintegral_indicator_one hSm]
  refine (lintegral_mono hpt).trans ?_
  rw [hint]
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hSμ zero_le)).trans ?_
  have hb0 : 0 ≤ b₁ := by rw [hb₁]; positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hb0 (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the good part
  have hgoodb : b₁ ≤ C₁ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    have h := three_pow_cap_div_le h8
    have e : b₁ = C₁ * G ^ 2 * Q ^ 2 * (((3 : ℝ) ^ k) ^ (4 * d - 1) / 3 ^ n) := by
      rw [hb₁, hC₁, hK₄]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  -- the bad part
  have hbad : 4 * M ^ 2 * (Cp * (2 * 3 ^ (n - k) + 29) ^ d * Real.exp (-c * (3 : ℝ) ^ k)) ≤
      C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    set t : ℝ := 3 ^ n with ht
    set u : ℝ := 3 ^ k with hu
    have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
    have ht0 : 0 < t := by linarith
    have hu0 : 0 < u := by positivity
    have hexp : Real.exp (-c * u) ≤ KB * (u⁻¹) ^ B := by
      have := hKBk k
      rwa [Real.rpow_one] at this
    have htk : t ^ (5 * d) ≤ 3 ^ B * u ^ B := by
      rw [ht, hu, ← pow_mul, ← pow_mul, ← pow_add]
      refine pow_le_pow_right₀ (by norm_num) ?_
      have h1 : n * (5 * d) ≤ 8 * d * (k + 1) * (5 * d) := Nat.mul_le_mul_right _ hnk.le
      have h2 : 8 * d * (k + 1) * (5 * d) = 40 * d ^ 2 + k * (40 * d ^ 2) := by ring
      rw [hB]
      linarith
    have hinv : t ^ (5 * d) * (u⁻¹) ^ B ≤ 3 ^ B := by
      rw [inv_pow]
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    have hnk' : (2 * (3 : ℝ) ^ (n - k) + 29) ^ d ≤ 31 ^ d * t ^ d := by
      have h1 : (3 : ℝ) ^ (n - k) ≤ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have h3 : 2 * (3 : ℝ) ^ (n - k) + 29 ≤ 31 * t := by linarith
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h3 d
    have hM2 : M ^ 2 = 4 * d ^ 2 * K₄ * t ^ (2 * (2 * d - 1)) * G ^ 2 * Q ^ 2 := by
      rw [hMdef, hK₄]
      ring
    have htpow : t ^ (2 * (2 * d - 1)) * t ^ d * t ≤ t ^ (5 * d) := by
      rw [← pow_add, ← pow_succ]
      exact pow_le_pow_right₀ ht1 (by omega)
    have hlast : t⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [ht]; exact inv_three_pow_le_three_rpow n
    have hA : 0 ≤ 16 * d ^ 2 * K₄ * G ^ 2 * Q ^ 2 * Cp * 31 ^ d * KB := by positivity
    have key : t ^ (2 * (2 * d - 1)) * t ^ d * (u⁻¹) ^ B ≤ 3 ^ B * t⁻¹ := by
      rw [le_mul_inv_iff₀ ht0]
      calc t ^ (2 * (2 * d - 1)) * t ^ d * (u⁻¹) ^ B * t
          = (t ^ (2 * (2 * d - 1)) * t ^ d * t) * (u⁻¹) ^ B := by ring
        _ ≤ t ^ (5 * d) * (u⁻¹) ^ B := mul_le_mul_of_nonneg_right htpow (by positivity)
        _ ≤ 3 ^ B := hinv
    calc 4 * M ^ 2 * (Cp * (2 * 3 ^ (n - k) + 29) ^ d * Real.exp (-c * (3 : ℝ) ^ k))
        ≤ 4 * M ^ 2 * (Cp * (31 ^ d * t ^ d) * (KB * (u⁻¹) ^ B)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hnk' hCp)
            hexp (Real.exp_pos _).le (by positivity)) (by positivity)
      _ = (16 * d ^ 2 * K₄ * G ^ 2 * Q ^ 2 * Cp * 31 ^ d * KB) *
            (t ^ (2 * (2 * d - 1)) * t ^ d * (u⁻¹) ^ B) := by rw [hM2]; ring
      _ ≤ (16 * d ^ 2 * K₄ * G ^ 2 * Q ^ 2 * Cp * 31 ^ d * KB) * (3 ^ B * t⁻¹) :=
          mul_le_mul_of_nonneg_left key hA
      _ = C₂ * G ^ 2 * Q ^ 2 * t⁻¹ := by rw [hC₂]; ring
      _ ≤ C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hlast (by positivity)
  have e : (C₁ + C₂) * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) =
      C₁ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) +
        C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by ring
  rw [e]
  exact add_le_add hgoodb hbad

end Rigidity.Percolation
