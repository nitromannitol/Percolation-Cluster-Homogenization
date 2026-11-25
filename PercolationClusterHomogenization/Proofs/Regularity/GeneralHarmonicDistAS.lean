import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicDist

/-!
# The harmonic approximation (7.7) of the coarsened function on triadic cubes, almost surely

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Steps 1 and 2, in every dimension
`d ≥ 2`: almost surely, for `3^j` above a minimal scale `𝒳 ≤ O_s(θ)` and `u` harmonic on
`𝒞_∞ ∩ B_R`, `√d 3^{j+4} ≤ R`,
`inf_{w ∈ Ā(□_j)} ‖[u]_𝒫 - w‖_{L̲²(□_j)} ≤ C 3^{-jα} inf_a ‖u - a‖_{L̲²(C_*(□_{j+3}))}`
(`cubeHarmonicDistAS_holds`), with `Ā(□_j)` the functions harmonic for the lattice Laplacian on
`□_j`.

The inputs are Theorem 1 in every dimension with the discrete homogenized solution
(`cubeHomogenizationError_holds`), the minimal scales of Proposition 2.4
(`cubeMinimalScales_holds`, `cubeRegularityScales_holds`), the density of the infinite cluster and
the Meyers estimate. The homogenized solution `w` on `□_{j+1}` is compared with `[u]_𝒫` on `□_j` by
`cubeL2_coarse_sub_homogenized_sq_le`, the gradient norm of Theorem 1 is bounded by
`cubeGradNorm_le`, and the sizes of the partition cubes are at most `3^{β(j+1)}`,
`β = min(α, 1) / (2d)`, which replaces the Hölder step with the `L^{p'}` interpolation of the
source. The planar form is `planarHarmonicDistTwo_of_homogenizationError`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeHC LatticeProb.Percolation Rigidity.External
open Rigidity.Percolation Rigidity.Dirichlet Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open Rigidity.Proofs.Cluster.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- The exponents of the two terms of `cubeL2_coarse_sub_homogenized_sq_le` with `δ = x^β`,
`d β ≤ α`, `β ≤ 1/2`, `x ≥ 1`. -/
theorem rpow_rate_bounds (hd : 0 < d) {x β α : ℝ} (hx : 1 ≤ x) (hβ0 : 0 < β) (hβα : d * β ≤ α)
    (hβ1 : β ≤ 1 / 2) :
    (x ^ β) ^ d * (x ^ (-α)) ^ 2 ≤ x ^ (-β) ∧ (x ^ β) ^ 2 / x ^ 2 ≤ x ^ (-β) := by
  have hx0 : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have e1 : (x ^ β) ^ d = x ^ (β * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  have e2 : (x ^ (-α)) ^ 2 = x ^ (-2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have e3 : (x ^ β) ^ 2 = x ^ (2 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have e4 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  constructor
  · rw [e1, e2, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith
  · rw [e3, e4, ← Real.rpow_sub hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    linarith

/-- `T = 3^{i - d}` satisfies the condition of `abs_grad_le_of_cubeInterior_cube` for `i ≥ d`. -/
theorem three_pow_sub_condition (hd : 0 < d) {i : ℕ} (hid : d ≤ i) :
    2 * (((d * (3 ^ (i - d) + 2) : ℕ) : ℤ)) + 2 * ((3 ^ (i - d) : ℕ) : ℤ) + 3 ≤ 16 * 3 ^ i := by
  have hdi : 3 ^ i = 3 ^ d * 3 ^ (i - d) := by rw [← pow_add]; congr 1; omega
  have hd3 : d + 1 ≤ 3 ^ d := by
    have := Nat.lt_pow_self (n := d) (by norm_num : 1 < 3)
    omega
  have hdd : d ≤ 3 ^ i := (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans
    (Nat.pow_le_pow_right (by norm_num) hid)
  have hT1 : 1 ≤ 3 ^ (i - d) := Nat.one_le_pow _ _ (by norm_num)
  have key : 2 * (d * (3 ^ (i - d) + 2)) + 2 * 3 ^ (i - d) + 3 ≤ 16 * 3 ^ i := by
    have h1 : (d + 1) * 3 ^ (i - d) ≤ 3 ^ i := by
      rw [hdi]; exact Nat.mul_le_mul_right _ hd3
    nlinarith
  exact_mod_cast key

set_option maxHeartbeats 400000 in
/-- **(7.7) on one cube** from Theorem 1 at the scale `i + 3`: for `w` harmonic on the interior of
`□_{i+3}` with the energy and error bounds of Theorem 1, partition cubes of side at most
`(3^{i+3})^β`, `d β ≤ α`, `β ≤ 1/2`, and the bound `M ≤ c 3^{-(i+2)} ‖u - a‖` of the gradient
norm for every `a`, `inf_w ‖[u]_𝒫 - w‖_{L̲²(□_{i+2})} ≤ K 3^{-(i+2)β/2} Γ_{i+5}`. -/
theorem cubeHarmonicDist_le_of_theoremOne_cube (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (u : C → ℝ) {i : ℕ} (hid : d ≤ i)
    (hres : PartitionResolved ω ⟨i + 3, 0⟩) {w : Vertex d → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {α β : ℝ} (hβ0 : 0 < β)
    (hβα : d * β ≤ α) (hβ1 : β ≤ 1 / 2)
    (hδ : ∀ y ∈ triadicCubeFinset d (i + 3) 0,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ ((3 : ℝ) ^ (i + 3)) ^ β)
    (hsmall : ∀ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCube ω y).scale ≤ i)
    {Ch c M : ℝ} (hCh : 0 ≤ Ch) (hM0 : 0 ≤ M)
    (hE : innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube
      w / ((3 : ℝ) ^ (i + 3)) ^ d ≤ Ch * M ^ 2)
    (hL : (3 : ℝ) ^ (-((i + 3 : ℕ) : ℝ)) * √((∑ x ∈ crossingClusterVertices ω ⟨i + 3, 0⟩,
        (Rigidity.Section3.extend C u x - w x) ^ 2) / ((3 : ℝ) ^ (i + 3)) ^ d) ≤
      Ch * (3 : ℝ) ^ (-(α * ((i + 3 : ℕ) : ℝ))) * M)
    (hMb : ∀ a : ℝ, M ≤ c / 3 ^ (i + 2) *
      clusterCubeL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a)) :
    cubeHarmonicDist d (i + 2) (partitionCoarse C u) ≤
      √(9 * c ^ 2 * (2 * 3 ^ d * Ch ^ 2 + 2 * (d : ℝ) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
        ((3 : ℝ) ^ (d + 3)) ^ d * Ch)) / ((3 : ℝ) ^ (i + 2)) ^ (β / 2) *
        clusterCubeOsc C u (i + 2 + 3) := by
  set x : ℝ := (3 : ℝ) ^ (i + 3) with hxdef
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < 3 ^ (i - d) := Nat.pos_of_ne_zero (by positivity)
  set T : ℕ := 3 ^ (i - d) with hTdef
  have hTi := three_pow_sub_condition hd hid
  have hδ0 : 0 ≤ x ^ β := Real.rpow_nonneg hx0.le _
  have hP' : (3 : ℝ) ^ (-(α * ((i + 3 : ℕ) : ℝ))) = x ^ (-α) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hP'] at hL
  have hsq := cubeL2_coarse_sub_homogenized_sq_le hd hP C u hT0 hTi hres hw hδ0 hδ hsmall
    hE hL
  -- the ratio `(3^{i+3})^d / T^d`
  have hratio : x ^ d / (T : ℝ) ^ d = ((3 : ℝ) ^ (d + 3)) ^ d := by
    have hTr : (T : ℝ) = 3 ^ (i - d) := by rw [hTdef]; push_cast; rfl
    have e : x = 3 ^ (d + 3) * (T : ℝ) := by
      rw [hxdef, hTr, ← pow_add]; congr 1; omega
    rw [e, mul_pow, mul_div_assoc, div_self (by positivity), mul_one]
  rw [hratio] at hsq
  obtain ⟨hb1, hb2⟩ := rpow_rate_bounds hd hx1 hβ0 hβα hβ1
  set K₀ : ℝ := 9 * c ^ 2 * (2 * 3 ^ d * Ch ^ 2 + 2 * (d : ℝ) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
    ((3 : ℝ) ^ (d + 3)) ^ d * Ch) with hK₀def
  have hK₀ : 0 ≤ K₀ := by positivity
  have hD := (ciInf_le (f := fun F : cubeLatticeHarmonic d (i + 2) =>
    cubeL2 d (i + 2) (partitionCoarse C u - F))
    ⟨0, fun _ ⟨_, hF⟩ => hF ▸ cubeL2_nonneg _ _⟩ ⟨w, mem_cubeLatticeHarmonic_of_cubeInterior hw⟩)
  have hall : ∀ a : ℝ, cubeHarmonicDist d (i + 2) (partitionCoarse C u) ≤
      √K₀ / ((3 : ℝ) ^ (i + 2)) ^ (β / 2) *
        clusterCubeL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a) := by
    intro a
    refine hD.trans ?_
    set Lc := clusterCubeL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a) with hLc
    have hLc0 : 0 ≤ Lc := clusterCubeL2_nonneg _ _ _
    have hMa := hMb a
    rw [← hLc] at hMa
    have hM2 : M ^ 2 ≤ (c / 3 ^ (i + 2) * Lc) ^ 2 := pow_le_pow_left₀ hM0 hMa 2
    have h32 : (3 : ℝ) ^ (i + 2) = x / 3 := by
      have e3 : (3 : ℝ) ^ (i + 3) = 3 ^ (i + 2) * 3 := by ring
      rw [hxdef, e3]; field_simp
    have hM2' : M ^ 2 ≤ 9 * c ^ 2 * Lc ^ 2 / x ^ 2 := by
      calc M ^ 2 ≤ (c / 3 ^ (i + 2) * Lc) ^ 2 := hM2
        _ = 9 * c ^ 2 * Lc ^ 2 / x ^ 2 := by rw [h32]; field_simp; ring
    have hcoef0 : 0 ≤ 2 * (x ^ β) ^ d * 3 ^ d * x ^ 2 * Ch ^ 2 * (x ^ (-α)) ^ 2 +
        2 * (d : ℝ) ^ 2 * (x ^ β) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
          ((3 : ℝ) ^ (d + 3)) ^ d * Ch := by positivity
    have hsq' : cubeL2 d (i + 2) (fun y => partitionCoarse C u y - w y) ^ 2 ≤
        K₀ * x ^ (-β) * Lc ^ 2 := by
      refine hsq.trans ?_
      calc (2 * (x ^ β) ^ d * 3 ^ d * x ^ 2 * Ch ^ 2 * (x ^ (-α)) ^ 2 +
            2 * (d : ℝ) ^ 2 * (x ^ β) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
              ((3 : ℝ) ^ (d + 3)) ^ d * Ch) * M ^ 2
          ≤ (2 * (x ^ β) ^ d * 3 ^ d * x ^ 2 * Ch ^ 2 * (x ^ (-α)) ^ 2 +
            2 * (d : ℝ) ^ 2 * (x ^ β) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
              ((3 : ℝ) ^ (d + 3)) ^ d * Ch) * (9 * c ^ 2 * Lc ^ 2 / x ^ 2) :=
            mul_le_mul_of_nonneg_left hM2' hcoef0
        _ = 9 * c ^ 2 * Lc ^ 2 * (2 * 3 ^ d * Ch ^ 2 * ((x ^ β) ^ d * (x ^ (-α)) ^ 2) +
            2 * (d : ℝ) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d * ((3 : ℝ) ^ (d + 3)) ^ d * Ch *
              ((x ^ β) ^ 2 / x ^ 2)) := by
            field_simp
        _ ≤ 9 * c ^ 2 * Lc ^ 2 * (2 * 3 ^ d * Ch ^ 2 * x ^ (-β) +
            2 * (d : ℝ) ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d * ((3 : ℝ) ^ (d + 3)) ^ d * Ch *
              x ^ (-β)) := by
            gcongr
        _ = K₀ * x ^ (-β) * Lc ^ 2 := by rw [hK₀def]; ring
    have hxβ : x ^ (-β) = (x ^ (β / 2))⁻¹ ^ 2 := by
      rw [← Real.rpow_natCast, Real.inv_rpow (Real.rpow_nonneg hx0.le _),
        ← Real.rpow_neg (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
      ring_nf
    have h3le : (3 : ℝ) ^ (i + 2) ≤ x := by
      rw [hxdef]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hx2 : ((3 : ℝ) ^ (i + 2)) ^ (β / 2) ≤ x ^ (β / 2) :=
      Real.rpow_le_rpow (by positivity) h3le (by positivity)
    have hpos2 : 0 < ((3 : ℝ) ^ (i + 2)) ^ (β / 2) := by positivity
    have hsqrt : cubeL2 d (i + 2) (fun y => partitionCoarse C u y - w y) ≤
        √K₀ / x ^ (β / 2) * Lc := by
      have h0 : 0 ≤ √K₀ / x ^ (β / 2) * Lc := by positivity
      rw [← Real.sqrt_sq (cubeL2_nonneg _ _), ← Real.sqrt_sq h0]
      apply Real.sqrt_le_sqrt
      calc cubeL2 d (i + 2) (fun y => partitionCoarse C u y - w y) ^ 2
          ≤ K₀ * x ^ (-β) * Lc ^ 2 := hsq'
        _ = (√K₀ / x ^ (β / 2) * Lc) ^ 2 := by
            rw [hxβ, mul_pow, div_pow, Real.sq_sqrt hK₀]; ring
    calc cubeL2 d (i + 2) (partitionCoarse C u - w)
        = cubeL2 d (i + 2) (fun y => partitionCoarse C u y - w y) := rfl
      _ ≤ √K₀ / x ^ (β / 2) * Lc := hsqrt
      _ ≤ √K₀ / ((3 : ℝ) ^ (i + 2)) ^ (β / 2) * Lc := by
          gcongr
  have hK' : 0 ≤ √K₀ / ((3 : ℝ) ^ (i + 2)) ^ (β / 2) := by positivity
  rw [clusterCubeOsc, Real.mul_iInf_of_nonneg hK']
  exact le_ciInf hall


/-- The harmonic approximation (7.7) of the proof of Armstrong–Dario, Lemma 7.1, on the cubes
`□_j` of `ℤᵈ`, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for the
functions harmonic on `𝒞_∞ ∩ B_R`, `√d 3^{j+4} ≤ R`. -/
def CubeHarmonicDistAS (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s θ C₁ α : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ C₁ ∧ 0 < α ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → Real.sqrt d * 3 ^ (j + 4) ≤ R →
            cubeHarmonicDist d j (partitionCoarse (uniqueInfiniteComponent h) u) ≤
              C₁ / ((3 : ℝ) ^ j) ^ α * clusterCubeOsc (uniqueInfiniteComponent h) u (j + 3)

set_option maxHeartbeats 400000 in
/-- **The harmonic approximation (7.7) on triadic cubes almost surely**, from Theorem 1 in every
dimension with the discrete homogenized solution and the minimal scales of Proposition 2.4, for
`p_c(d) < p < 1`, `d ≥ 2`. -/
theorem cubeHarmonicDistAS_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : CubeHarmonicDistAS d p := by
  have hd0 : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ := cubePartitionSizeScale_holds hd hpc
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := cubeRegularityScales_holds hd hpc
  obtain ⟨ε, hε, t, ht, hMK⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  obtain ⟨sh, αh, Ch, σ, hsh, hαh, hCh, -, -, Xh, hXhm, hXh0, hXhos, hXhae⟩ :=
    cubeHomogenizationError_holds hd hpc (p' := 2 * (1 + ε / 2)) (by linarith)
  obtain ⟨α', hα'def⟩ : ∃ a : ℝ, a = min αh 1 := ⟨_, rfl⟩
  have hα'0 : 0 < α' := by rw [hα'def]; exact lt_min hαh one_pos
  have hα'α : α' ≤ αh := by rw [hα'def]; exact min_le_left _ _
  have hα'1 : α' ≤ 1 := by rw [hα'def]; exact min_le_right _ _
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = α' / (2 * d) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβα : d * β ≤ αh := by
    rw [hβdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hβ1 : β ≤ 1 / 2 := by
    rw [hβdef, div_le_iff₀ (by positivity)]; nlinarith
  have ht₆ : 1 ≤ d / β - d := by
    rw [hβdef, div_div_eq_mul_div, le_sub_iff_add_le, le_div_iff₀ hα'0]
    nlinarith
  obtain ⟨r₆, C₆, hr₆, hC₆, M₆, hM₆m, hM₆0, hM₆os, hM₆ae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc _ ht₆
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (Real.sqrt d)
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  obtain ⟨θa, hθa, ha⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hsh hr₁ hCh hθ₁ hXhm hM₁m
    hXhos hM₁os
  obtain ⟨θb, hθb, hb⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hs₃ hs₄ hθ₃ hθ₄ hM₃m hM₄m
    hM₃os hM₄os
  obtain ⟨θc, hθc, hc⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hr₆ hr₆ hC₆ (by positivity)
    hM₆m measurable_const hM₆os
    (isOsBond_const (p := p) (d := d) (by positivity : (0 : ℝ) < 3 ^ (d + 7)) hr₆)
  obtain ⟨θab, hθab, hab⟩ := Rigidity.Dirichlet.IsOsBond.exists_max (lt_min hsh hr₁)
    (lt_min hs₃ hs₄) hθa hθb (hXhm.max hM₁m) (hM₃m.max hM₄m) ha hb
  obtain ⟨θX, hθX, hXos⟩ := Rigidity.Dirichlet.IsOsBond.exists_max
    (lt_min (lt_min hsh hr₁) (lt_min hs₃ hs₄)) (lt_min hr₆ hr₆) hθab hθc
    ((hXhm.max hM₁m).max (hM₃m.max hM₄m)) (hM₆m.max measurable_const) hab hc
  -- the constant
  set c : ℝ := CM ^ (1 / (2 * (1 + ε / 2))) * √(8 * d * 3 ^ d) with hcdef
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = √(9 * c ^ 2 * (2 * 3 ^ d * Ch ^ 2 + 2 * (d : ℝ) ^ 2 * 4 ^ d *
      (10 * (d : ℝ)) ^ d * ((3 : ℝ) ^ (d + 3)) ^ d * Ch)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact Real.sqrt_nonneg _
  refine ⟨_, θX, K, β / 2, lt_min (lt_min (lt_min hsh hr₁) (lt_min hs₃ hs₄)) (lt_min hr₆ hr₆),
    hθX, hK0, by positivity, _, ((hXhm.max hM₁m).max (hM₃m.max hM₄m)).max
      (hM₆m.max measurable_const),
    fun ω => (hXh0 ω).trans ((le_max_left _ _).trans ((le_max_left _ _).trans
      (le_max_left _ _))), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₃ae, hM₄ae, hM₆ae, hXhae] with
    ω hcells hω₁ hω₃' hω₄ hω₆ hωh h
  obtain ⟨hP, hω₃⟩ := hω₃'
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  set C := uniqueInfiniteComponent h with hCdef
  intro R u hu j hj hjR
  have hinf := uniqueInfiniteComponent_infinite h
  have hjh : Xh ω ≤ 3 ^ j :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hj
  have hj1 : M₁ ω ≤ 3 ^ j :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hj
  have hj3 : M₃ ω ≤ 3 ^ j :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hj
  have hj4 : M₄ ω ≤ 3 ^ j :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hj
  have hj6 : M₆ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_right _ _)).trans hj
  have hj7 : (3 : ℝ) ^ (d + 7) ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_right _ _)).trans hj
  have hj7' : d + 7 ≤ j := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hj7
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have hid : d ≤ i := by omega
  have hle : ∀ m, i + 2 ≤ m → (3 : ℝ) ^ (i + 2) ≤ 3 ^ m := fun m hm =>
    pow_le_pow_right₀ (by norm_num) hm
  have hres : ∀ m, i + 2 ≤ m → PartitionResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset d m 0 := mem_cubeFinset_iff_vertices.2 hz
    have := hω₃ m (hj3.trans (hle m hm)) z hz'
    show (partitionCube ω z).scale ≤ m
    omega
  have hκ : 0 < theta d p / 2 := by positivity
  have hsub : ∀ m, i + 2 ≤ m → ∀ x ∈ crossingClusterVertices ω ⟨m, 0⟩, x ∈ C.supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_cubeFinset_of_clusterCubeDensity hd0 C hκ (hω₄ h)
      (hj4.trans (hle m hm))
    exact mem_supp_of_mem_crossingClusterVertices hd0 hP (hres m hm) C hinf
      (mem_cubeFinset_iff_vertices.1 hx₀) x₀.2 hx
  have hsucc : ∀ m, i + 2 ≤ m → ∀ x ∈ triadicCubeFinset d m 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩ := fun m hm x hx hxC =>
    mem_crossingClusterVertices_succ hd0 hP C hinf (hω₃ m (hj3.trans (hle m hm))) hx hxC
  have hincl : ∀ m n, i + 2 ≤ m → m < n →
      crossingClusterVertices ω ⟨m, 0⟩ ⊆ crossingClusterVertices ω ⟨n, 0⟩ := by
    intro m n hm hmn x hx
    have hxC := hsub m hm x hx
    have hx1 : x ∈ triadicCubeFinset d (n - 1) 0 :=
      mem_cubeFinset_mono (by omega) (mem_cubeFinset_of_mem_crossingClusterVertices hx)
    have := hsucc (n - 1) (by omega) x hx1 hxC
    rwa [show n - 1 + 1 = n by omega] at this
  have hjR' : Real.sqrt d * 3 ^ (i + 3 + 3) ≤ R := by
    rw [show i + 3 + 3 = i + 2 + 4 by ring]; exact hjR
  have hharm6 := harm_on_cube_of_isHarmonicInBall hd0 hu hjR'
  have hharm5 : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (i + 2 + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0 := fun x hx hxs =>
    hharm6 x hx (mem_cubeFinset_mono (by omega) hxs)
  -- the scales of the partition cubes
  have hsize6 : ∀ m : ℕ, i + 2 ≤ m → ∀ y ∈ triadicCubeFinset d m 0,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ ((3 : ℝ) ^ m) ^ β := by
    intro m hm y hy
    have hb6 := (hω₆ m (hj6.trans (hle m hm))).2 y (mem_cubeFinset_iff_vertices.1 hy)
    have e : (d : ℝ) * m / (d + (d / β - d)) = β * m := by
      rw [show (d : ℝ) + (d / β - d) = d / β by ring]
      field_simp
    rw [e] at hb6
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), mul_comm (m : ℝ) β]
    exact hb6
  have htwo : ∀ m : ℕ, i + 2 ≤ m → ∀ y ∈ triadicCubeFinset d m 0,
      (partitionCube ω y).scale * 2 ≤ m := by
    intro m hm y hy
    refine two_mul_le_of_three_pow_le_rpow_half' ((hsize6 m hm y hy).trans ?_)
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hβ1
  have hsc : ∀ x ∈ triadicCubeFinset d (i + 2 + 3) 0, (partitionCube ω x).scale ≤ i + 2 :=
    fun x hx => by have := htwo (i + 2 + 3) (by omega) x hx; omega
  have hsmall : ∀ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCube ω y).scale ≤ i :=
    fun y hy => by have := htwo (i + 2) le_rfl y hy; omega
  have hδ : ∀ y ∈ triadicCubeFinset d (i + 3) 0,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ ((3 : ℝ) ^ (i + 3)) ^ β :=
    hsize6 (i + 3) (by omega)
  have hin : ∀ x, x ∈ C.supp → (∀ k, 2 * |x k| < 17 * 3 ^ (i + 2)) →
      x ∈ crossingClusterVertices ω ⟨i + 2 + 3, 0⟩ := fun x hxC hx =>
    mem_crossingClusterVertices_inner_cube hd0 hP C hinf hsc hxC hx
  -- the Meyers estimate
  have hω₁' := hω₁ (i + 3 + 1) (hj1.trans (hle _ (by omega)))
  have hsizeM : ∀ z ∈ cube (i + 3 + 1) (0 : Vertex d), sc ω z ≤ i + 3 + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half' (hω₁'.2.1 z hz)
    omega
  have hMeyj := meyers_on_cube hMey C u (hsub (i + 3 + 2) (by omega)) hharm6 (sc ω) hcell hnb
    hrh hsizeM (hω₁ (i + 3) (hj1.trans (hle _ (by omega)))).1
  -- Theorem 1 at the scale `i + 3`
  obtain ⟨-, -, hfun⟩ := hωh (i + 3) (hjh.trans (hle _ (by omega)))
  have hharm3 := extend_mem_cubeHarmonic (U := ⟨i + 3, 0⟩) C (u := u) (hsub (i + 3) (by omega))
    fun x hx hxV _ => hharm6 x hx
      (mem_cubeFinset_mono (by omega) (mem_cubeFinset_of_mem_crossingClusterVertices hxV))
  obtain ⟨w, hw, -, hE, hL⟩ := hfun (Rigidity.Section3.extend C u) hharm3
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = cubeGradNorm ω (i + 3) (2 * (1 + ε / 2))
      (Rigidity.Section3.extend C u) := ⟨_, rfl⟩
  rw [← hMdef] at hE hL
  have hM0 : 0 ≤ M := by rw [hMdef]; exact cubeGradNorm_nonneg _ _ _ _
  have hMb : ∀ a : ℝ, M ≤ c / 3 ^ (i + 2) *
      clusterCubeL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a) := by
    intro a
    have hMb := cubeGradNorm_le C u (j := i + 2) (hincl _ _ (by omega) (by omega))
      (hsub (i + 2 + 3) (by omega)) hin hharm5 hq hCM hMeyj a
    rw [hMdef]
    exact hMb
  have hfin := cubeHarmonicDist_le_of_theoremOne_cube hd0 hP C u hid (hres (i + 3) (by omega))
    hw hβ0 hβα hβ1 hδ hsmall hCh.le hM0 hE hL hMb
  rw [← hKdef] at hfin
  exact hfin

end Rigidity.Proofs.Regularity
