import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.LatticeClusterLipschitz
import LatticeProb.Prob.Percolation.MeasurableCorrectorGradients
import PercolationClusterHomogenization.Proofs.Lattice.ConfigurationExtension

/-!
# Lemma 3.1: the dihedral symmetry of the lattice and of the corrected planes

Step `step:3.1-reflection` of Lemma 3.1 (paper L841-859 of the corrected draft).

* An automorphism `φ` of the nearest-neighbor graph of `ℤ^d` permutes the bonds, hence acts on
  the configurations by permuting coordinates; this action preserves the product Bernoulli law
  (`Measure.infinitePi_map_piCongrLeft`), and `φ` is a graph isomorphism from the open graph of
  `ω` onto the open graph of the transported configuration. It therefore transports the open
  components, their infinitude, the unique infinite cluster, the Laplacian and the Lipschitz
  bounds for the graph distance.
* The signed permutations `x ↦ (sᵢ x_{π i})ᵢ` of the coordinates are such automorphisms; they
  are Euclidean isometries fixing the origin and transport the affine function `x ↦ q · x` to
  `x ↦ q' · x` with `q'ᵢ = sᵢ q_{π i}`. Hence they transport corrected planes of slope `q` to
  corrected planes of slope `q'`, and the set of `L`-Lipschitz slopes covariantly.
* The reflections `T_j` and the coordinate transpositions are signed permutations; since the law
  is invariant, a slope which is almost surely `L`-Lipschitz has almost surely `L`-Lipschitz
  images.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Section3

variable {d : ℕ}

section Automorphism

variable (φ : nearestNeighborGraph d ≃g nearestNeighborGraph d)

/-- A nearest-neighbor pair is carried to a nearest-neighbor pair, as an `ℓ¹`-distance-one
statement. -/
theorem latticeL1Dist_map_eq_one {x y : Vertex d} (h : latticeL1Dist x y = 1) :
    latticeL1Dist (φ x) (φ y) = 1 :=
  lattice_adj_iff_l1Dist.mp (φ.map_adj_iff.mpr (lattice_adj_iff_l1Dist.mpr h))

/-- The image of a bond under a lattice automorphism. -/
def bondMapFun (e : Bond d) : Bond d :=
  ⟨Sym2.map φ e.val, by
    obtain ⟨x, y, hxy, h1⟩ := e.property
    exact ⟨φ x, φ y, by rw [hxy, Sym2.map_mk], latticeL1Dist_map_eq_one φ h1⟩⟩

/-- A lattice automorphism permutes the bonds. -/
def bondMap : Bond d ≃ Bond d where
  toFun := bondMapFun φ
  invFun := bondMapFun φ.symm
  left_inv e := Subtype.ext (by
    simp only [bondMapFun, Sym2.map_map, Function.comp_def, RelIso.symm_apply_apply,
      Sym2.map_id', id_eq])
  right_inv e := Subtype.ext (by
    simp only [bondMapFun, Sym2.map_map, Function.comp_def, RelIso.apply_symm_apply,
      Sym2.map_id', id_eq])

/-- The bond of an edge is carried to the bond of the image edge. -/
theorem bondMap_bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondMap φ (bondOfAdjacent h) = bondOfAdjacent (φ.map_adj_iff.mpr h) :=
  Subtype.ext (Sym2.map_mk φ x y)

/-- The action of a lattice automorphism on configurations: the state of the image of a bond is
the state of the bond. -/
def configurationMap : Configuration d ≃ᵐ Configuration d :=
  MeasurableEquiv.piCongrLeft (fun _ : Bond d => Bool) (bondMap φ)

/-- The transported configuration evaluated at the image of a bond. -/
theorem configurationMap_apply_bondMap (ω : Configuration d) (e : Bond d) :
    configurationMap φ ω (bondMap φ e) = ω e :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Bond d => Bool) (bondMap φ) ω e

/-- The product Bernoulli law is invariant under the action of lattice automorphisms. -/
theorem latticeBondLaw_map_configurationMap (p : unitInterval) :
    (latticeBondLaw d p).map (configurationMap φ) = latticeBondLaw d p :=
  Measure.infinitePi_map_piCongrLeft (fun _ : Bond d => bernoulliMeasure true false p)
    (bondMap φ)

/-- The action of a lattice automorphism preserves the product Bernoulli law. -/
theorem measurePreserving_configurationMap (p : unitInterval) :
    MeasurePreserving (configurationMap φ) (latticeBondLaw d p) (latticeBondLaw d p) where
  measurable := (configurationMap φ).measurable
  map_eq := latticeBondLaw_map_configurationMap φ p

/-- An edge is open exactly when its image is open in the transported configuration. -/
theorem openGraph_adj_configurationMap_iff (ω : Configuration d) (x y : Vertex d) :
    (openGraph (configurationMap φ ω)).Adj (φ x) (φ y) ↔ (openGraph ω).Adj x y := by
  constructor
  · rintro ⟨h, ho⟩
    refine ⟨φ.map_adj_iff.mp h, ?_⟩
    rw [← configurationMap_apply_bondMap φ ω (bondOfAdjacent (φ.map_adj_iff.mp h)),
      bondMap_bondOfAdjacent]
    exact ho
  · rintro ⟨h, ho⟩
    refine ⟨φ.map_adj_iff.mpr h, ?_⟩
    rwa [← bondMap_bondOfAdjacent, configurationMap_apply_bondMap]

/-- A lattice automorphism is an isomorphism of open graphs onto the transported
configuration. -/
def openGraphMap (ω : Configuration d) : openGraph ω ≃g openGraph (configurationMap φ ω) where
  toEquiv := φ.toEquiv
  map_rel_iff' := openGraph_adj_configurationMap_iff φ ω _ _

end Automorphism

section Iso

variable {ω ω' : Configuration d} {C : OpenComponent ω} {D : OpenComponent ω'}

end Iso

section SignedPermutation

variable (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)

/-- The square of a sign is one. -/
theorem units_int_mul_self (u : ℤˣ) : (u : ℤ) * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- A sign has absolute value one. -/
theorem abs_units_int (u : ℤˣ) : |(u : ℤ)| = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- The signed permutation `x ↦ (sᵢ x_{π i})ᵢ` of the lattice. -/
def signedPermVertex : Vertex d ≃ Vertex d where
  toFun x i := (s i : ℤ) * x (π i)
  invFun y k := (s (π.symm k) : ℤ) * y (π.symm k)
  left_inv x := by
    funext k
    simp only [Equiv.apply_symm_apply, ← mul_assoc, units_int_mul_self, one_mul]
  right_inv y := by
    funext i
    simp only [Equiv.symm_apply_apply, ← mul_assoc, units_int_mul_self, one_mul]

/-- Signed permutations preserve the `ℓ¹` distance. -/
theorem latticeL1Dist_signedPermVertex (x y : Vertex d) :
    latticeL1Dist (signedPermVertex π s x) (signedPermVertex π s y) = latticeL1Dist x y := by
  unfold latticeL1Dist
  have hs (i : Fin d) (a b : ℤ) : |(s i : ℤ) * a - (s i : ℤ) * b| = |a - b| := by
    rw [← mul_sub, abs_mul, abs_units_int, one_mul]
  simp only [signedPermVertex, Equiv.coe_fn_mk, hs]
  exact Equiv.sum_comp π (fun i => |x i - y i|)

/-- Signed permutations are automorphisms of the nearest-neighbor lattice. -/
def signedPermIso : nearestNeighborGraph d ≃g nearestNeighborGraph d where
  toEquiv := signedPermVertex π s
  map_rel_iff' := by
    intro x y
    rw [lattice_adj_iff_l1Dist, lattice_adj_iff_l1Dist]
    exact congrArg (· = 1) (latticeL1Dist_signedPermVertex π s x y) |>.to_iff

/-- The action of a signed permutation on slopes, `q'ᵢ = sᵢ q_{π i}`. -/
def signedPermSlope (q : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ((s i : ℤ) : ℝ) * q (π i)

/-- The affine function of slope `q` is carried to the affine function of slope `q'`. -/
theorem sum_signedPermSlope_mul (q : Fin d → ℝ) (x : Vertex d) :
    ∑ i, signedPermSlope π s q i * (signedPermIso π s x i : ℝ) = ∑ i, q i * (x i : ℝ) := by
  have hs (i : Fin d) : ((s i : ℤ) : ℝ) * ((s i : ℤ) : ℝ) = 1 := by
    exact_mod_cast units_int_mul_self (s i)
  have hterm (i : Fin d) : signedPermSlope π s q i * (signedPermIso π s x i : ℝ) =
      q (π i) * (x (π i) : ℝ) := by
    change ((s i : ℤ) : ℝ) * q (π i) * (((s i : ℤ) * x (π i) : ℤ) : ℝ) = _
    push_cast
    linear_combination (q (π i) * (x (π i) : ℝ)) * hs i
  simp only [hterm]
  exact Equiv.sum_comp π (fun i => q i * (x i : ℝ))

/-- Signed permutations fix the origin. -/
theorem signedPermIso_zero : signedPermIso π s (0 : Vertex d) = 0 := by
  funext i
  change (s i : ℤ) * 0 = 0
  exact mul_zero _

variable {ω : Configuration d}

end SignedPermutation

end Rigidity.Proofs.S3
