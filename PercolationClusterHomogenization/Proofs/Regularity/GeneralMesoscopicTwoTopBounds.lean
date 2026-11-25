import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicTwoTop

/-!
# The top-scale bounds in the proof of Lemma 7.3 at `k = 2` in every dimension

With `T = R / (8A)`, `U = [u]_𝒫` and `G = R^{-1} inf_a ‖u - a‖_R`, `‖·‖_R` being
`R^{-d/2} ‖·‖_{ℓ²(𝒞_∞ ∩ B_R)}` (Armstrong and Dario, arXiv:1609.09431v2, proof of Lemma 7.3,
Step 2), in every dimension:

* `coarse_top_oneD`: for a lattice harmonic function `v` on `B_{4T}` within `B + η` of `U` and a
  harmonic quadratic polynomial `W`, the distance of `U` to `W` on `B_T` is at most
  `C_t (B + η) + C₁ (√K₂ ‖u - W‖_R + d K₁ Λ)`, `Λ` the slope of `W` on `B_R`;
* `coarse_top_boundsD`: if the distance of `U` to the lattice harmonic functions on `B_{4T}` is at
  most `B`, the excesses of `U` on `B_T` over the lattice harmonic quadratic functions and over the
  constants are at most `C_t B + C_a D̃_2(R) + C_b G` and `C_t B + C_a D̃_0(R)`.

These are the planar statements of `PlanarMesoscopicTwoTopBounds` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The lower radius of the top-scale bounds. -/
noncomputable def topScaleD (d : ℕ) (A : ℝ) : ℝ :=
  8 * A * (meanValueScale d + 6 * Real.sqrt d + 3)

theorem meanValueScale_nonneg (d : ℕ) : 0 ≤ meanValueScale d := by
  unfold meanValueScale; positivity

/-- The facts on `T = R / (8A)` used at the top scale. -/
theorem topScaleD_facts {A R : ℝ} (hA : 2 ≤ A) (hR : topScaleD d A ≤ R) :
    meanValueScale d ≤ R / (8 * A) ∧ 6 * Real.sqrt d ≤ R / (8 * A) ∧ 3 ≤ R / (8 * A) ∧
      4 * (R / (8 * A)) ≤ R / 2 ∧ 1 ≤ R ∧ 4 * Real.sqrt d ≤ R := by
  have hA0 : 0 < A := by linarith
  have hm := meanValueScale_nonneg d
  have hsd := Real.sqrt_nonneg (d : ℝ)
  have hT : meanValueScale d + 6 * Real.sqrt d + 3 ≤ R / (8 * A) := by
    rw [le_div_iff₀ (by positivity)]; rw [topScaleD] at hR; linarith
  have hT3 : 3 ≤ R / (8 * A) := by linarith
  have hR8 : 8 * A * (R / (8 * A)) = R := by field_simp
  refine ⟨by linarith, by linarith, hT3, ?_, ?_, ?_⟩
  · have : 4 * (R / (8 * A)) = R / (2 * A) := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hR0 : 0 < R := by
      have := mul_pos (by positivity : (0 : ℝ) < 8 * A) (by linarith : (0 : ℝ) < R / (8 * A))
      linarith
    nlinarith
  · have := mul_le_mul_of_nonneg_left hT3 (by positivity : (0 : ℝ) ≤ 8 * A)
    nlinarith
  · have h6 : 6 * Real.sqrt d ≤ R / (8 * A) := by linarith
    have := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 8 * A)
    nlinarith

/-- The constant `C₁ = C_MV (2 √d)^d (8A)^d` of the top-scale bound. -/
noncomputable def topSumConstD (d : ℕ) (A : ℝ) : ℝ :=
  meanValueConst d * (2 * Real.sqrt d) ^ d * (8 * A) ^ d

theorem topSumConstD_nonneg (d : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ topSumConstD d A := by
  have := meanValueConst_nonneg d
  unfold topSumConstD; positivity

/-- **One harmonic quadratic polynomial at the top scale.** -/
theorem coarse_top_oneD [NeZero d] (hP : PartitionEvent ω) (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {A K₁ K₂ R S' B η : ℝ} (hA : 2 ≤ A) (hK₂ : 0 ≤ K₂)
    (hR : topScaleD d A ≤ R) (hS'0 : 0 ≤ S') (hS' : Real.sqrt d * S' ≤ R / 4)
    (hsize : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
        (3 : ℝ) ^ (partitionCube ω y).scale ≤ S')
    (hm₁ : ∑ y ∈ latticeBallPointsD 0 R, (3 : ℝ) ^ (partitionCube ω y).scale ≤ K₁ * R ^ d)
    (hm₂ : ∑ y ∈ latticeBallPointsD 0 R, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤ K₂ * R ^ d)
    {v : latticeComponent d → ℝ} (hvm : v ∈ latticeHarmonicClass (0 : Vertex d)
      (4 * (R / (8 * A))))
    (hvb : componentBallL2 (latticeComponent d) 0 (4 * (R / (8 * A)))
      ((fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) - v) ≤ B + η)
    (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.trace = 0) :
    componentBallL2 (latticeComponent d) 0 (R / (8 * A))
        (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val -
          latticeQuadFunD a p M x.val) ≤
      coarseTopConstD d * (B + η) + topSumConstD d A * (Real.sqrt K₂ *
          clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun x => latticeQuadFunD a p M x.val)) +
        topSumConstD d A * (d * K₁) * quadSlopeD p M R := by
  have hA0 : 0 < A := by linarith
  obtain ⟨hTm, hT6, hT3, h4T, hR1, -⟩ := topScaleD_facts hA hR
  have hR0 : 0 < R := by linarith
  obtain ⟨T, hT⟩ : ∃ x : ℝ, x = R / (8 * A) := ⟨_, rfl⟩
  rw [← hT] at hTm hT6 hT3 h4T hvm hvb ⊢
  have hT0 : 0 < T := by linarith
  have h1 := componentBallL2_coarse_sub_quad_leD (partitionCoarse (uniqueInfiniteComponent h) u)
    hTm hT6 hT3 hvm a p hM
  have h2 := sum_abs_coarse_sub_quad_top_leD hP h u (ρ := 4 * T) hR0 hS'0 hS' h4T hsize hm₁ hm₂
    hK₂ a p M
  obtain ⟨E, hE⟩ : ∃ x, x = clusterBallVolumeL2 (uniqueInfiniteComponent h) R
      (u - fun x => latticeQuadFunD a p M x.val) := ⟨_, rfl⟩
  rw [← hE] at h2 ⊢
  obtain ⟨S₄, hS₄⟩ : ∃ x, x = ∑ y ∈ latticeBallPointsD 0 (4 * T),
      |partitionCoarse (uniqueInfiniteComponent h) u y - latticeQuadFunD a p M y| := ⟨_, rfl⟩
  rw [← hS₄] at h1 h2
  have hRT : (R / T) ^ d = (8 * A) ^ d := by rw [hT]; congr 1; field_simp
  have hCMV0 : 0 ≤ meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d := by
    have := meanValueConst_nonneg d; positivity
  have h3 : meanValueConst d * (2 * Real.sqrt d) ^ d / T ^ d * S₄ ≤
      topSumConstD d A * (Real.sqrt K₂ * E) + topSumConstD d A * (d * K₁) * quadSlopeD p M R := by
    have := mul_le_mul_of_nonneg_left h2 hCMV0
    refine this.trans (le_of_eq ?_)
    rw [topSumConstD, ← hRT, div_pow]
    field_simp
  have hfirst := mul_le_mul_of_nonneg_left hvb (coarseTopConstD_nonneg d)
  linarith

/-- **The top-scale bounds.** -/
theorem coarse_top_boundsD [NeZero d] {A K₁ K₂ κ : ℝ} (hA : 2 ≤ A) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hκ : 0 < κ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω)
      (h : HasUniqueInfiniteOpenComponent ω) (ℓ R S' B : ℝ) (u : uniqueInfiniteComponent h → ℝ),
      topScaleD d A ≤ R → quadLocality d (capFraction d κ) * max ℓ 1 ≤ R → 0 ≤ S' →
      Real.sqrt d * S' ≤ R / 4 →
      (∀ y : Vertex d,
        dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
          (3 : ℝ) ^ (partitionCube ω y).scale ≤ S') →
      (∑ y ∈ latticeBallPointsD 0 R, (3 : ℝ) ^ (partitionCube ω y).scale ≤ K₁ * R ^ d) →
      (∑ y ∈ latticeBallPointsD 0 R, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤ K₂ * R ^ d) →
      ClusterCubeDensity (uniqueInfiniteComponent h) 0 (quadLocality d (capFraction d κ)) ℓ κ →
      ballDist (componentBallSeminorm (latticeComponent d) 0)
          (latticeHarmonicClass (0 : Vertex d) (4 * (R / (8 * A)))) (4 * (R / (8 * A)))
          (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤ B →
      ballExcess (componentBallSeminorm (latticeComponent d) 0) (latticeHarmonicQuadratic d)
          (R / (8 * A)) (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤
        coarseTopConstD d * B + Ca * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
          Cb * ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) / R) ∧
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
          (clusterConstants (latticeComponent d))
          (R / (8 * A)) (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤
        coarseTopConstD d * B + Ca * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hA0 : 0 < A := by linarith
  set Kc := quadSlopeConstD d κ with hKc
  have hKc0 : 0 ≤ Kc := quadSlopeConstD_nonneg hd hκ
  set C₁ := topSumConstD d A with hC₁
  have hC₁0 : 0 ≤ C₁ := topSumConstD_nonneg d hA0.le
  refine ⟨C₁ * (Real.sqrt K₂ + d * K₁ * Kc), C₁ * (d * K₁ * Kc), by positivity, by positivity,
    ?_⟩
  intro ω hP h ℓ R S' B u hR hRq hS'0 hS' hsize hm₁ hm₂ hcube hB
  obtain ⟨-, -, -, -, hR1, -⟩ := topScaleD_facts hA hR
  have hR0 : 0 < R := by linarith
  obtain ⟨U, hU⟩ : ∃ f : latticeComponent d → ℝ,
      f = fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val := ⟨_, rfl⟩
  rw [← hU] at hB ⊢
  obtain ⟨D0R, hD0R⟩ : ∃ x : ℝ,
      x = ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) :=
    ⟨_, rfl⟩
  rw [← hD0R]
  have hD0R0 : 0 ≤ D0R := by rw [hD0R]; exact iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _
  have hCt := coarseTopConstD_nonneg d
  -- a near approximant at `4T`
  have hv : ∀ η : ℝ, 0 < η → ∃ v ∈ latticeHarmonicClass (0 : Vertex d) (4 * (R / (8 * A))),
      componentBallL2 (latticeComponent d) 0 (4 * (R / (8 * A))) (U - v) ≤ B + η := by
    intro η hη
    haveI : Nonempty (latticeHarmonicClass (0 : Vertex d) (4 * (R / (8 * A)))) :=
      ⟨⟨0, zero_mem_latticeHarmonicClass (0 : Vertex d) _⟩⟩
    obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right
      (ballDist (componentBallSeminorm (latticeComponent d) 0)
        (latticeHarmonicClass (0 : Vertex d) (4 * (R / (8 * A)))) (4 * (R / (8 * A))) U) hη)
    refine ⟨v, v.2, ?_⟩
    rw [← componentBallSeminorm_apply]
    exact hv.le.trans (by linarith)
  constructor
  · -- `k = 2`
    apply le_of_forall_pos_le_add_mul hCt
    intro η hη
    obtain ⟨v, hvm, hvb⟩ := hv η hη
    rw [hU] at hvb
    have key : ∀ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        ballExcess (componentBallSeminorm (latticeComponent d) 0) (latticeHarmonicQuadratic d)
            (R / (8 * A)) U ≤
          (coarseTopConstD d * B + C₁ * (d * K₁ * Kc) * (D0R / R) + coarseTopConstD d * η) +
          C₁ * (Real.sqrt K₂ + d * K₁ * Kc) *
            clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w) := by
      intro w
      obtain ⟨a, p, M, hM, hw⟩ := w.2
      have hwe : (w : uniqueInfiniteComponent h → ℝ) = fun x => latticeQuadFunD a p M x.val :=
        funext fun x => hw x
      rw [hwe]
      have hwl := mem_latticeHarmonicQuadratic_of_trace_eq_zeroD a p hM
      have h0 := ballExcess_le (componentBallSeminorm (latticeComponent d) 0)
        (latticeHarmonicQuadratic d) (s := R / (8 * A)) (u := U) hwl
      rw [componentBallSeminorm_apply] at h0
      have e0 : (U - fun x => latticeQuadFunD a p M x.val) =
          fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val -
            latticeQuadFunD a p M x.val := by rw [hU]; rfl
      rw [e0] at h0
      have h1 := coarse_top_oneD hP h u hA hK₂ hR hS'0 hS' hsize hm₁ hm₂ hvm hvb a p hM
      rw [← hC₁] at h1
      have hslope := quadSlopeD_le_of_clusterCubeDensity (uniqueInfiniteComponent h) hd hκ hcube
        hRq a p M u
      rw [← hKc, ← hD0R] at hslope
      obtain ⟨E, hE⟩ : ∃ x, x = clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun x => latticeQuadFunD a p M x.val) := ⟨_, rfl⟩
      rw [← hE] at hslope h1 ⊢
      have hE0 : 0 ≤ E := by rw [hE]; exact Real.sqrt_nonneg _
      obtain ⟨Λ, hΛ⟩ : ∃ x, x = quadSlopeD p M R := ⟨_, rfl⟩
      rw [← hΛ] at hslope h1
      have hc0 : 0 ≤ C₁ * (d * K₁) := by positivity
      have hthird : C₁ * (d * K₁) * Λ ≤ C₁ * (d * K₁ * Kc) * (D0R / R) +
          C₁ * (d * K₁ * Kc) * E := by
        have hΛle : Λ ≤ Kc * (D0R + E) / R := by rw [le_div_iff₀ hR0]; exact hslope
        have h5 := mul_le_mul_of_nonneg_left hΛle hc0
        refine h5.trans ?_
        have h7 : C₁ * (d * K₁) * (Kc * (D0R + E) / R) =
            C₁ * (d * K₁ * Kc) * (D0R / R) + C₁ * (d * K₁ * Kc) * (E / R) := by
          field_simp
        rw [h7]
        have h8 : E / R ≤ E := div_le_self hE0 hR1
        have h9 := mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ C₁ * (d * K₁ * Kc))
        linarith
      have e1 : C₁ * (Real.sqrt K₂ + d * K₁ * Kc) * E =
          C₁ * (Real.sqrt K₂ * E) + C₁ * (d * K₁ * Kc) * E := by ring
      rw [e1]
      linarith
    have := le_add_mul_iInf (by positivity : (0 : ℝ) ≤ C₁ * (Real.sqrt K₂ + d * K₁ * Kc)) key
    linarith
  · -- `k = 0`
    apply le_of_forall_pos_le_add_mul hCt
    intro η hη
    obtain ⟨v, hvm, hvb⟩ := hv η hη
    rw [hU] at hvb
    have key : ∀ c : ℝ,
        ballExcess (componentBallSeminorm (latticeComponent d) 0)
          (clusterConstants (latticeComponent d)) (R / (8 * A)) U ≤
          (coarseTopConstD d * B + coarseTopConstD d * η) +
            C₁ * (Real.sqrt K₂ + d * K₁ * Kc) *
              clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
      intro c
      have hc : (fun _ : latticeComponent d => c) ∈ clusterConstants (latticeComponent d) :=
        ⟨c, fun _ => rfl⟩
      have h0 := ballExcess_le (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) (s := R / (8 * A)) (u := U) hc
      rw [componentBallSeminorm_apply] at h0
      have hq : ∀ y : Vertex d, latticeQuadFunD c 0 0 y = c := fun y => by
        simp [latticeQuadFunD, quadForm]
      have h1 := coarse_top_oneD hP h u hA hK₂ hR hS'0 hS' hsize hm₁ hm₂ hvm hvb c 0 (M := 0)
        (by simp)
      rw [← hC₁] at h1
      have hU0 : componentBallL2 (latticeComponent d) 0 (R / (8 * A)) (U - fun _ => c) =
          componentBallL2 (latticeComponent d) 0 (R / (8 * A))
            (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val -
              latticeQuadFunD c 0 0 x.val) := by
        congr 1; funext x; simp only [Pi.sub_apply, hq, hU]
      have hE : clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun x => latticeQuadFunD c 0 0 x.val) =
          clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
        congr 1; funext x; simp only [Pi.sub_apply, hq]
      rw [hE, quadSlopeD_zero, mul_zero, add_zero] at h1
      rw [hU0] at h0
      obtain ⟨E, hE'⟩ : ∃ x, x = clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun _ => c) := ⟨_, rfl⟩
      rw [← hE'] at h1 ⊢
      have hE0 : 0 ≤ E := by rw [hE']; exact Real.sqrt_nonneg _
      have hCa'' : C₁ * (Real.sqrt K₂ * E) ≤ C₁ * (Real.sqrt K₂ + d * K₁ * Kc) * E := by
        have : 0 ≤ C₁ * (d * K₁ * Kc) * E := by positivity
        nlinarith
      linarith
    have := le_add_mul_iInf (by positivity : (0 : ℝ) ≤ C₁ * (Real.sqrt K₂ + d * K₁ * Kc)) key
    rw [← hD0R] at this
    linarith

end Rigidity.Proofs.Regularity
