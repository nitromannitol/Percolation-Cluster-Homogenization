import Mathlib

/-!
# Statement-level audit vocabulary for the `OrderZero` comparator

Verbatim copy of the vocabulary block of `HomogenizationAudit/OrderZero/Challenge.lean` (between
`VOCABULARY-BEGIN` and `VOCABULARY-END`), Mathlib-only; a mechanical copy, not hand-edited. The two
blocks must stay byte-identical so that the comparator's constant-by-constant closure check passes.
-/

open MeasureTheory Filter

namespace PercolationClusterHomogenization
namespace StatementAudit
namespace OrderZero

-- VOCABULARY-BEGIN
noncomputable section

/-! ## The lattice (`LatticeProb/Site.lean`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- A unit vector is not zero. -/
theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)⟩

/-! ## Bernoulli bond percolation
(`LatticeProb/Prob/Percolation/LatticeBondModel.lean`, `LatticeBondProbability.lean`) -/

section BondModel

open ProbabilityTheory

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- Unordered nearest-neighbor bonds, with the literal ℓ¹-distance-one carrier. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A deterministic assignment of open or closed status to every genuine lattice bond. -/
abbrev Configuration (d : ℕ) := Bond d → Bool

/-- The nearest-neighbor graph already supplied by the lattice library. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- Adjacent vertices are at `ℓ¹` distance one. -/
theorem l1Dist_eq_one_of_adj {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    (∑ i, |x i - y i|) = 1 := by
  obtain ⟨i, rfl | rfl⟩ := h <;> simp [unit, Pi.single_apply, apply_ite abs]

/-- The bond determined by adjacent vertices; no endpoint ordering is chosen. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, l1Dist_eq_one_of_adj h⟩

/-- Reversing the endpoint presentation does not change its bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- The canonical product Bernoulli law on genuine nearest-neighbor bonds. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)

end BondModel

/-! ## The open graph and its components (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

section BondGraph

variable {d : ℕ}

/-- The graph retaining exactly the bonds assigned `true` by the configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

/-- Every open neighbor set is finite: it lies among the `2d` lattice neighbors. -/
theorem openGraph_neighborSet_finite (ω : Configuration d) (x : Vertex d) :
    ((openGraph ω).neighborSet x).Finite := by
  refine (Set.finite_range (fun q : Fin d × Bool =>
    if q.2 then x + unit q.1 else x - unit q.1)).subset ?_
  rintro y ⟨⟨i, hi | hi⟩, -⟩
  · exact ⟨(i, true), by simp [hi]⟩
  · exact ⟨(i, false), by simp [hi]⟩

/-- Every open neighbor set is a finite subset of the lattice neighbor set. -/
noncomputable instance openGraphLocallyFinite (ω : Configuration d) :
    (openGraph ω).LocallyFinite :=
  fun x => Set.Finite.fintype (openGraph_neighborSet_finite ω x)

/-- Actual connected components of the configuration's open graph. -/
abbrev OpenComponent (ω : Configuration d) := (openGraph ω).ConnectedComponent

/-- Existence and uniqueness of an infinite open component, without a chosen carrier. -/
def HasUniqueInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃! C : OpenComponent ω, C.supp.Infinite

/-- The graph on the actual vertices of an open connected component. -/
abbrev componentGraph {ω : Configuration d} (C : OpenComponent ω) := C.toSimpleGraph

/-- Inclusion of component neighbors into the open graph's neighbors is injective. -/
def componentNeighborEmbedding {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (componentGraph C).neighborSet x ↪ (openGraph ω).neighborSet x.val where
  toFun y := ⟨y.val.val, y.property⟩
  inj' := by
    intro y z h
    have hv : y.val.val = z.val.val :=
      congrArg (fun t : (openGraph ω).neighborSet x.val => t.val) h
    exact Subtype.ext (Subtype.ext hv)

/-- Component graphs inherit local finiteness through inclusion of their neighbors. -/
noncomputable instance componentGraphLocallyFinite {ω : Configuration d} (C : OpenComponent ω) :
    (componentGraph C).LocallyFinite := fun x =>
  Fintype.ofInjective (componentNeighborEmbedding C x) (componentNeighborEmbedding C x).injective

/-- The source Laplacian on a component uses functions on its actual vertex subtype. -/
noncomputable def componentLaplacian {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : C) : ℝ :=
  ∑ y ∈ (componentGraph C).neighborFinset x, (u y - u x)

end BondGraph

/-! ## The critical probability and the unique infinite cluster
(`LatticeBondInfiniteEvent.lean`, `LatticeBondCritical.lean`, `LatticeUniqueCluster.lean`,
`LatticeUniqueClusterEvent.lean`, `LatticeClusterLipschitz.lean`) -/

section Cluster

variable {d : ℕ}

/-- The actual component of `x` has infinitely many vertices. -/
def infiniteComponentEvent (x : Vertex d) : Set (Configuration d) :=
  {ω | ((openGraph ω).connectedComponentMk x).supp.Infinite}

/-- The probability that the actual open component of the origin is infinite. -/
noncomputable def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (latticeBondLaw d p).real (infiniteComponentEvent 0)

/-- The critical probability is literally the real infimum of positive-theta parameters. -/
noncomputable def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

/-- The event of existence and uniqueness of an infinite actual open component. -/
def uniqueInfiniteComponentEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω}

variable {ω : Configuration d}

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

end Cluster

/-! ## Euclidean balls and the normalized `L²` average
(`LatticeClusterBall.lean`, `LatticeClusterL2.lean`) -/

section Balls

variable {d : ℕ}

/-- The coordinatewise integer inclusion into Euclidean space, with its Euclidean metric. -/
def latticeEuclideanEmbedding : Vertex d ↪ EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  inj' := by
    intro x y h
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    change (x i : ℝ) = (y i : ℝ) at hi
    exact_mod_cast hi

/-- An ambient open Euclidean ball contains only finitely many lattice vertices. -/
theorem finite_latticeEuclideanBall (z : Vertex d) (r : ℝ) :
    {x : Vertex d | dist (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding z) < r}.Finite := by
  have hbox := Set.Finite.pi' (fun i : Fin d =>
    Set.finite_Icc (z i - ⌈r⌉) (z i + ⌈r⌉))
  apply hbox.subset
  intro x hx i
  have hi := PiLp.norm_apply_le
    (latticeEuclideanEmbedding x - latticeEuclideanEmbedding z) i
  change |(x i : ℝ) - (z i : ℝ)| ≤
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding z‖ at hi
  have hb : |(x i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉ : ℝ) :=
    (hi.trans_lt (show ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding z‖ < r from hx)).le.trans (Int.le_ceil r)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor
  · exact_mod_cast (by linarith : (z i : ℝ) - (⌈r⌉ : ℝ) ≤ (x i : ℝ))
  · exact_mod_cast (by linarith : (x i : ℝ) ≤ (z i : ℝ) + (⌈r⌉ : ℝ))

/-- The finite component-vertex carrier of an open Euclidean ball. -/
theorem finite_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    {x : C | dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding z) < r}.Finite :=
  (finite_latticeEuclideanBall z r).preimage Subtype.val_injective.injOn

/-- The literal intersection of a component with an open Euclidean ball, on its vertex subtype. -/
def componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) : Finset C :=
  (finite_componentEuclideanBall C z r).toFinset

variable {ω : Configuration d}

/-- The source normalized L² expression on the literal finite component ball. -/
def componentBallL2 (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2) /
    ((componentEuclideanBall C z r).card : ℝ))

/-- The normalized sum is a finite Euclidean norm with its cardinality factor. -/
theorem componentBallL2_eq_norm_div (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r u =
      ‖(WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x) :
        EuclideanSpace ℝ (componentEuclideanBall C z r))‖ /
        Real.sqrt ((componentEuclideanBall C z r).card : ℝ) := by
  classical
  rw [componentBallL2, Real.sqrt_div (Finset.sum_nonneg (fun x _ => sq_nonneg (u x))),
    EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 2
  exact (Finset.sum_coe_sort (componentEuclideanBall C z r) (fun x => (u x) ^ 2)).symm

/-- Minkowski's inequality for the normalized `L²` average. -/
theorem componentBallL2_add_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u v : C → ℝ) :
    componentBallL2 C z r (u + v) ≤
      componentBallL2 C z r u + componentBallL2 C z r v := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div,
    componentBallL2_eq_norm_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact norm_add_le
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => v x))

/-- Scalar multiplication scales the normalized `L²` average by the absolute scalar. -/
theorem componentBallL2_smul (C : OpenComponent ω) (z : Vertex d) (r a : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r (a • u) = |a| * componentBallL2 C z r u := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div, ← mul_div_assoc]
  congr 1
  exact norm_smul a
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))

end Balls

/-! ## Harmonic functions of controlled growth and corrected planes
(`LatticeHarmonicGrowth.lean`, `CorrectedPlaneCharacterization.lean`) -/

section Growth

variable {d : ℕ} {ω : Configuration d}

/-- The literal normalized L² growth condition at all real radii tending to infinity. -/
def componentL2Subpolynomial (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) : Prop :=
  Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)

/-- On nonnegative radii the scaled normalized `L²` average is nonnegative. -/
theorem componentL2_scaled_nonneg (C : OpenComponent ω) (k : ℕ) (u : C → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) (Real.sqrt_nonneg _)

/-- The zero function satisfies the growth condition. -/
theorem componentL2Subpolynomial_zero (C : OpenComponent ω) (k : ℕ) :
    componentL2Subpolynomial C k 0 := by
  simp [componentL2Subpolynomial, componentBallL2]

/-- The growth condition is closed under addition. -/
theorem componentL2Subpolynomial_add (C : OpenComponent ω) (k : ℕ)
    {u v : C → ℝ} (hu : componentL2Subpolynomial C k u)
    (hv : componentL2Subpolynomial C k v) : componentL2Subpolynomial C k (u + v) := by
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C k _ hR⟩
  · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
    calc
      (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R (u + v) ≤
          (R ^ (k + 1))⁻¹ * (componentBallL2 C 0 R u + componentBallL2 C 0 R v) :=
        mul_le_mul_of_nonneg_left (componentBallL2_add_le C 0 R u v)
          (inv_nonneg.mpr (pow_nonneg hR _))
      _ = (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u +
          (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R v := mul_add _ _ _
  · simpa only [add_zero] using hu.add hv

/-- The growth condition is closed under scalar multiplication. -/
theorem componentL2Subpolynomial_smul (C : OpenComponent ω) (k : ℕ)
    {u : C → ℝ} (hu : componentL2Subpolynomial C k u) (a : ℝ) :
    componentL2Subpolynomial C k (a • u) := by
  have h := hu.const_mul |a|
  simp only [mul_zero] at h
  exact h.congr (fun R => by rw [componentBallL2_smul]; ring)

/-- The component Laplacian is additive. -/
theorem componentLaplacian_add (C : OpenComponent ω) (u v : C → ℝ) (x : C) :
    componentLaplacian C (u + v) x = componentLaplacian C u x + componentLaplacian C v x := by
  simp only [componentLaplacian, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The component Laplacian commutes with scalar multiplication. -/
theorem componentLaplacian_smul (C : OpenComponent ω) (a : ℝ) (u : C → ℝ) (x : C) :
    componentLaplacian C (a • u) x = a * componentLaplacian C u x := by
  simp only [componentLaplacian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Source A_k on an actual open component, with literal exponent k+1 and averaged L². -/
def harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) : Submodule ℝ (C → ℝ) where
  carrier := {u | (∀ x, componentLaplacian C u x = 0) ∧ componentL2Subpolynomial C k u}
  zero_mem' := ⟨fun x => by simp [componentLaplacian], componentL2Subpolynomial_zero C k⟩
  add_mem' := by
    rintro u v ⟨hu, hgu⟩ ⟨hv, hgv⟩
    exact ⟨fun x => by rw [componentLaplacian_add, hu, hv, add_zero],
      componentL2Subpolynomial_add C k hgu hgv⟩
  smul_mem' := by
    rintro a u ⟨hu, hgu⟩
    exact ⟨fun x => by rw [componentLaplacian_smul, hu, mul_zero],
      componentL2Subpolynomial_smul C k hgu a⟩

end Growth

/-! ## Theorem 2 (iii) of Armstrong and Dario at order zero (`LatticeProb/External/`) -/

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 0`**, for Bernoulli bond percolation with
zero-one conductances (`LatticeProb/External/`): for `d ≥ 2` and `p_c(d) < p < 1` there are
`s, θ, C > 0` and a random scale `X` with `E exp((X/θ)^s) ≤ 2` such that, almost surely, the
infinite cluster exists and is unique, the harmonic functions on it of sublinear growth are the
constants, and every function harmonic on the ball of radius `R ≥ 2X` of the cluster is
approximated at every scale `X ≤ r ≤ R/2` by a constant, with relative `L²` error at most
`C r / R`. -/
def ArmstrongDarioOrderZero : Prop :=
  ∀ (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) ∧
              Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) = 1 ∧
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ φ : uniqueInfiniteComponent h' → ℝ,
                    φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h') 0 ∧
                    ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                      componentBallL2 (uniqueInfiniteComponent h') 0 r (u - φ) ≤
                        C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u

end
-- VOCABULARY-END

end OrderZero
end StatementAudit
end PercolationClusterHomogenization
