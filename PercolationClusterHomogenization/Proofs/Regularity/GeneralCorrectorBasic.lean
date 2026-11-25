import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorConstruction
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds

/-!
# Correctors on the infinite cluster of `ℤᵈ`: slopes, increments and the order-zero regularity

The elementary bounds used to build the corrected planes of Theorem 2 (ii) of Armstrong and Dario
(arXiv:1609.09431v2) at `k = 1` in every dimension `d`:

* `abs_componentSlope_sub_le`, `abs_componentSlope_le`: the affine function `q · x` varies by at
  most `(∑ i, |q i|) R` over a distance `R`;
* `abs_corrector_sub_le`: the increment of the corrector `χ = u - q · x` between neighbours, from
  the approximation of `u` by constants at the scale `ρ` around a vertex (Remark after (1.19));
* `card_componentEuclideanBall_ge`: the cluster carries at least `κ 3^{d m}` vertices of the balls
  `B_{2 d 3^m}(x)` around the vertices of a box, from the density of the cluster in triadic cubes;
* `exists_origin_constant_approximation`, `exists_all_centres_constant_approximation`: Theorem 2
  (iii) at order zero (`armstrongDarioOrderZero_holds`) as an approximation by constants, at the
  origin and, by stationarity, at every centre.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The corrector `χ_q = u - q · x` of a function on a component. -/
noncomputable def componentCorrector (C : OpenComponent ω) (q : Fin d → ℝ) (u : C → ℝ) :
    C → ℝ :=
  fun x => u x - componentSlope C q x

theorem abs_componentSlope_sub_le (C : OpenComponent ω) (q : Fin d → ℝ) {x y : C} {R : ℝ}
    (h : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ≤ R) :
    |componentSlope C q y - componentSlope C q x| ≤ (∑ i, |q i|) * R := by
  unfold componentSlope
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    ((abs_sub_le_dist_latticeEuclideanEmbedding y.val x.val i).trans h) (abs_nonneg _)

theorem abs_componentSlope_le (C : OpenComponent ω) (q : Fin d → ℝ) {R : ℝ} {x : C}
    (hx : x ∈ componentEuclideanBall C 0 R) : |componentSlope C q x| ≤ (∑ i, |q i|) * R := by
  rw [mem_componentEuclideanBall] at hx
  unfold componentSlope
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex d) i
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h
  linarith

/-- The normalized norm on a ball against the one on a ball containing it. -/
theorem componentBallL2_le_of_subset (C : OpenComponent ω) {x z : Vertex d} {r R : ℝ}
    (hsub : componentEuclideanBall C x r ⊆ componentEuclideanBall C z R)
    (hpos : 0 < (componentEuclideanBall C x r).card) (f : C → ℝ) :
    componentBallL2 C x r f ≤
      Real.sqrt (((componentEuclideanBall C z R).card : ℝ) /
        ((componentEuclideanBall C x r).card : ℝ)) * componentBallL2 C z R f := by
  unfold componentBallL2
  have hn : (0 : ℝ) < (componentEuclideanBall C x r).card := by exact_mod_cast hpos
  have hN : (0 : ℝ) < (componentEuclideanBall C z R).card :=
    lt_of_lt_of_le hn (by exact_mod_cast Finset.card_le_card hsub)
  rw [← Real.sqrt_mul (div_nonneg hN.le hn.le)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_div_comm, mul_comm (↑(componentEuclideanBall C z R).card : ℝ),
    mul_div_mul_right _ _ hN.ne']
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) hn.le

/-- **Increments from the approximation by a constant** at the scale `ρ` around `x`. -/
theorem abs_sub_le_of_constant_approximation (C : OpenComponent ω) (x : Vertex d) (v : C → ℝ)
    {ρ c : ℝ} {x' y' : C} (hx' : x' ∈ componentEuclideanBall C x ρ)
    (hy' : y' ∈ componentEuclideanBall C x ρ) :
    |v y' - v x'| ≤ 2 * ((componentEuclideanBall C x ρ).card : ℝ) *
      componentBallL2 C x ρ (v - fun _ => c) := by
  have h1 := Rigidity.Proofs.S2.abs_le_card_mul_componentBallL2 C x ρ (v - fun _ => c) hy'
  have h2 := Rigidity.Proofs.S2.abs_le_card_mul_componentBallL2 C x ρ (v - fun _ => c) hx'
  simp only [Pi.sub_apply] at h1 h2
  calc |v y' - v x'| = |(v y' - c) - (v x' - c)| := by ring_nf
    _ ≤ |v y' - c| + |v x' - c| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **The gradient of the corrector at `x`** from the approximation of `u - a` by constants at the
scale `ρ` around `x`, for every constant `a`. -/
theorem abs_corrector_sub_le (C : OpenComponent ω) (q : Fin d → ℝ) (u : C → ℝ) (x : C)
    {ρ R C₀ : ℝ} (hR : 0 < R) (hC₀ : 0 ≤ C₀) (hρ : 0 ≤ ρ)
    (happ : ∀ a : ℝ, ∃ c : ℝ, componentBallL2 C x.val ρ ((fun y => u y - a) - fun _ => c) ≤
      C₀ * (ρ / R) * componentBallL2 C x.val R (fun y => u y - a))
    {y : C} (hx : x ∈ componentEuclideanBall C x.val ρ) (hy : y ∈ componentEuclideanBall C x.val ρ)
    (hyx : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ≤ 1) :
    |componentCorrector C q u y - componentCorrector C q u x| ≤
      2 * (2 * ρ + 3) ^ d * C₀ * (ρ / R) *
        (componentBallL2 C x.val R (componentCorrector C q u) + (∑ i, |q i|) * R) +
      ∑ i, |q i| := by
  obtain ⟨c, hc⟩ := happ (componentSlope C q x)
  have hinc := abs_sub_le_of_constant_approximation C x.val (fun y => u y - componentSlope C q x)
    (c := c) hx hy
  have hcard := card_componentEuclideanBall_le C x.val hρ
  have hL2 : componentBallL2 C x.val R (fun y => u y - componentSlope C q x) ≤
      componentBallL2 C x.val R (componentCorrector C q u) + (∑ i, |q i|) * R := by
    have e : (fun y => u y - componentSlope C q x) = fun y =>
        componentCorrector C q u y + (componentSlope C q y - componentSlope C q x) := by
      funext y; unfold componentCorrector; ring
    rw [e]
    refine (Rigidity.Proofs.S2.componentBallL2_add_le C x.val R _ _).trans ?_
    gcongr
    refine componentBallL2_le_of_abs_le C x.val R (by positivity) fun y hy => ?_
    have hd : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) < R := by
      rw [mem_componentEuclideanBall] at hy; exact hy
    exact abs_componentSlope_sub_le C q hd.le
  have hslope := abs_componentSlope_sub_le C q hyx
  have hL0 : 0 ≤ componentBallL2 C x.val ρ ((fun y => u y - componentSlope C q x) - fun _ => c) :=
    componentBallL2_nonneg _ _ _ _
  have hu : |u y - u x| ≤ 2 * (2 * ρ + 3) ^ d * C₀ * (ρ / R) *
      (componentBallL2 C x.val R (componentCorrector C q u) + (∑ i, |q i|) * R) := by
    have h1 : |u y - u x| ≤ 2 * ((componentEuclideanBall C x.val ρ).card : ℝ) *
        componentBallL2 C x.val ρ ((fun y => u y - componentSlope C q x) - fun _ => c) := by
      have : (u y - componentSlope C q x) - (u x - componentSlope C q x) = u y - u x := by ring
      rw [← this]; exact hinc
    calc |u y - u x| ≤ _ := h1
      _ ≤ 2 * (2 * ρ + 3) ^ d *
          (C₀ * (ρ / R) * componentBallL2 C x.val R (fun y => u y - componentSlope C q x)) := by
          gcongr
      _ ≤ 2 * (2 * ρ + 3) ^ d * (C₀ * (ρ / R) *
          (componentBallL2 C x.val R (componentCorrector C q u) + (∑ i, |q i|) * R)) := by
          gcongr
      _ = _ := by ring
  have e : componentCorrector C q u y - componentCorrector C q u x =
      (u y - u x) - (componentSlope C q y - componentSlope C q x) := by
    unfold componentCorrector; ring
  rw [e]
  calc |(u y - u x) - (componentSlope C q y - componentSlope C q x)|
      ≤ |u y - u x| + |componentSlope C q y - componentSlope C q x| := abs_sub _ _
    _ ≤ _ := by
        have h1 : (∑ i, |q i|) * 1 = ∑ i, |q i| := mul_one _
        linarith

/-- The index of the triadic cube of scale `m` containing `x`. -/
noncomputable def nearIndex (m : ℕ) (x : Vertex d) : Vertex d :=
  fun i => (x i + ((3 : ℤ) ^ m - 1) / 2) / 3 ^ m

theorem two_mul_abs_sub_nearIndex_lt (m : ℕ) (x : Vertex d) (i : Fin d) :
    2 * |x i - 3 ^ m * nearIndex m x i| < 3 ^ m := by
  have ho : (3 : ℤ) ^ m % 2 = 1 := Int.odd_iff.mp (Odd.pow ⟨1, by norm_num⟩)
  have hT : (0 : ℤ) < 3 ^ m := by positivity
  have hd := Int.emod_add_mul_ediv (x i + ((3 : ℤ) ^ m - 1) / 2) (3 ^ m)
  have h0 := Int.emod_nonneg (x i + ((3 : ℤ) ^ m - 1) / 2) hT.ne'
  have h1 := Int.emod_lt_of_pos (x i + ((3 : ℤ) ^ m - 1) / 2) hT
  have hh := Int.emod_add_mul_ediv ((3 : ℤ) ^ m) 2
  unfold nearIndex
  generalize (x i + ((3 : ℤ) ^ m - 1) / 2) % 3 ^ m = r at hd h0 h1
  generalize 3 ^ m * ((x i + ((3 : ℤ) ^ m - 1) / 2) / 3 ^ m) = P at hd ⊢
  rcases abs_cases (x i - P) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

theorem sqrt_le_self_of_neZero [NeZero d] : Real.sqrt (d : ℝ) ≤ d := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- **The cluster carries a fixed proportion of the balls around the vertices of a box.** -/
theorem card_componentEuclideanBall_ge [NeZero d] (C : OpenComponent ω) {Λ ℓ κ a : ℝ}
    (hcube : ClusterCubeDensity C 0 Λ ℓ κ) {m : ℕ} (hm : ℓ ≤ 3 ^ m) {x : Vertex d}
    (hx : ∀ i, |((x i : ℤ) : ℝ)| ≤ a * 3 ^ m) (hΛ : (d : ℝ) * (a + 1) < Λ) :
    κ * 3 ^ (d * m) ≤ (componentEuclideanBall C x (2 * d * 3 ^ m)).card := by
  have hT : (0 : ℝ) < 3 ^ m := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hsq := sqrt_le_self_of_neZero (d := d)
  have ha : 0 ≤ a := by
    have h0 := (abs_nonneg ((x 0 : ℤ) : ℝ)).trans (hx 0)
    exact nonneg_of_mul_nonneg_left h0 hT
  have hnear : ∀ i, |((x i : ℤ) : ℝ) - 3 ^ m * ((nearIndex m x i : ℤ) : ℝ)| < 3 ^ m / 2 := by
    intro i
    have h := two_mul_abs_sub_nearIndex_lt m x i
    have h' : ((2 * |x i - 3 ^ m * nearIndex m x i| : ℤ) : ℝ) < (((3 : ℤ) ^ m : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  have hcubeY : ∀ y ∈ triadicCube d m (nearIndex m x), ∀ i,
      |((y i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| ≤ 3 ^ m := by
    intro y hy i
    have h1 : |((y i : ℤ) : ℝ) - 3 ^ m * ((nearIndex m x i : ℤ) : ℝ)| < 3 ^ m / 2 := hy i
    have h2 := hnear i
    have a := abs_sub_le ((y i : ℤ) : ℝ) (3 ^ m * ((nearIndex m x i : ℤ) : ℝ)) ((x i : ℤ) : ℝ)
    rw [abs_sub_comm (3 ^ m * ((nearIndex m x i : ℤ) : ℝ)) ((x i : ℤ) : ℝ)] at a
    linarith
  have hin : ∀ y ∈ triadicCube d m (nearIndex m x),
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) <
        Λ * 3 ^ m := by
    intro y hy
    have hy0 : ∀ i, |((y i : ℤ) : ℝ) - latticeEuclideanEmbedding (0 : Vertex d) i| ≤
        (a + 1) * 3 ^ m := by
      intro i
      have e : latticeEuclideanEmbedding (0 : Vertex d) i = 0 := by
        simp [latticeEuclideanEmbedding]
      rw [e, sub_zero]
      have h1 := hcubeY y hy i
      have h2 := hx i
      have a := abs_sub_abs_le_abs_sub ((y i : ℤ) : ℝ) ((x i : ℤ) : ℝ)
      linarith
    have hd := dist_latticeEuclideanEmbedding_le (by positivity) hy0
    calc dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d))
        ≤ Real.sqrt d * ((a + 1) * 3 ^ m) := hd
      _ ≤ d * ((a + 1) * 3 ^ m) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (d * (a + 1)) * 3 ^ m := by ring
      _ < Λ * 3 ^ m := mul_lt_mul_of_pos_right hΛ hT
  have h := hcube m (nearIndex m x) hm hin
  have hle : (clusterCubePoints C 0 (Λ * 3 ^ m) m (nearIndex m x)).card ≤
      (componentEuclideanBall C x (2 * d * 3 ^ m)).card := by
    refine Finset.card_le_card fun y hy => ?_
    simp only [clusterCubePoints, mem_filter] at hy
    rw [mem_componentEuclideanBall]
    have hy' : y.val ∈ triadicCube d m (nearIndex m x) := fun i => hy.2 i
    have hxy : ∀ i, |((y.val i : ℤ) : ℝ) - latticeEuclideanEmbedding x i| ≤ 3 ^ m := by
      intro i
      exact hcubeY y.val hy' i
    have hd := dist_latticeEuclideanEmbedding_le (by positivity) hxy
    calc dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x)
        ≤ Real.sqrt d * 3 ^ m := hd
      _ ≤ d * 3 ^ m := mul_le_mul_of_nonneg_right hsq hT.le
      _ < 2 * d * 3 ^ m := by nlinarith
  exact h.trans (by exact_mod_cast hle)

/-- **The order-zero regularity at the origin** in every dimension `d ≥ 2`, as an approximation by
constants (Theorem 2 (iii) at `k = 0`). -/
theorem exists_origin_constant_approximation [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, hAE⟩ :=
    armstrongDarioOrderZero_holds d hd p hp hp1
  refine ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, ?_⟩
  filter_upwards [hAE] with ω hω
  obtain ⟨hex, hω⟩ := hω
  refine ⟨hex, ?_⟩
  intro h R hR u hu
  obtain ⟨hfinite, hrank, happ⟩ := hω h
  obtain ⟨φ, hφ, happrox⟩ := happ R hR u hu
  obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfinite hrank φ hφ
  refine ⟨c, ?_⟩
  intro r hr hRr
  simpa only [hc] using happrox r hr hRr

/-- **The order-zero regularity at every centre** in every dimension `d ≥ 2`: the minimal scale at
`z` is `𝒳 ∘ τ_{-z}`, with the same law. -/
theorem exists_all_centres_constant_approximation [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Vertex d → Configuration d → ℝ,
        (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
        (∀ z, Integrable (fun ω => Real.exp (Real.rpow (X z ω / θ) s))
          (latticeBondLaw d p)) ∧
        (∀ z, (∫ ω, Real.exp (Real.rpow (X z ω / θ) s) ∂latticeBondLaw d p) ≤ 2) ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ z : Vertex d,
              ∀ (R : ℝ), 2 * X z ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X z ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') z r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') z R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hXn, hXi, hXb, hAE⟩ :=
    exists_origin_constant_approximation hd p hp hp1
  let Y : Vertex d → Configuration d → ℝ := fun z ω => X (configurationTranslation (-z) ω)
  refine ⟨s, θ, C, hs, hθ, hC, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact hXm.comp (configurationTranslationMeasurableEquiv (-z)).measurable
  · intro z ω
    exact hXn _
  · intro z
    exact (measurePreserving_configurationTranslation p (-z)).integrable_comp_of_integrable hXi
  · intro z
    have he := (measurePreserving_configurationTranslation p (-z)).integral_comp
      (configurationTranslationMeasurableEquiv (-z)).measurableEmbedding
      (fun ω => Real.exp (Real.rpow (X ω / θ) s))
    exact he.trans_le hXb
  · have hall := ae_all_iff.mpr (fun z : Vertex d =>
      (measurePreserving_configurationTranslation p (-z)).quasiMeasurePreserving.ae hAE)
    filter_upwards [hAE, hall] with ω hω hz
    obtain ⟨h, _⟩ := hω
    refine ⟨h, ?_⟩
    intro h' z
    have ht := (hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h'
    exact origin_constant_approximation_translation z h' (Y z ω) C ((hz z).2 ht)

end Rigidity.Proofs.Regularity.GeneralDim
