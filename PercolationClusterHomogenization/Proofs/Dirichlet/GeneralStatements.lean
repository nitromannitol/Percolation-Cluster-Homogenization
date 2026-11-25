import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralChainBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuLimit
import PercolationClusterHomogenization.External.CorrectorQuantitative

/-!
# Theorem 1 of Armstrong and Dario in every dimension, and its two inputs on the cluster

This file states, as definitions of propositions, the quantitative homogenization of the Dirichlet
problem on the cluster of a cube of `ℤᵈ` (S. Armstrong and P. Dario, *Elliptic regularity and
quantitative homogenization on percolation clusters*, Comm. Pure Appl. Math. 71 (2018),
Theorem 1) and the two inputs on the cluster from which it is derived in Section 6 of the source,
for the partition into good cubes in every dimension `d`.

* `CubeMinimalScales d p`: the minimal scales of the partition (Proposition 2.4 of the source, the
  two bounds of (2.13)): for every `t ≥ 1` a random scale `𝓜_t ≤ O_s(C)` such that
  `3^m ≥ 𝓜_t` implies `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
  `size(□_𝒫(x)) ≤ 3^{dm/(d+t)}` for every `x ∈ □_m`.
* `CubeMesoscopicConvergence d p`: the convergence of `μ` and `ν` on the mesoscopic cubes of the
  proofs of Lemmas 6.2 and 6.3 above a random scale `𝒩 ≤ O_s(C)` (Definition 5.12, Proposition 5.13
  and (6.4)–(6.5) of the source), on the triadic subcubes of `□_m` of scale `⌈m/8⌉`.
* `CubeHomogenizationError d p p'`: Theorem 1 for the exponent `p' > 2`, with the discrete
  homogenized solution: `ā = σ I` and, for `3^m ≥ 𝒳` and every `u` harmonic on `C_*(□_m)` at the
  vertices whose lattice neighbours lie in `□_m`, a discrete harmonic function `u_hom` on the
  lattice cube `□_m` equal to `u` on `C_*(□_m) ∩ ∂□_m` with `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²` and
  `3^{-m} (|□_m|⁻¹ Σ_{C_*(□_m)} |u − u_hom|²)^{1/2} ≤ C 3^{-mα} M`,
  `M = (|□_m|⁻¹ Σ_{C_*(□_m)} |∇u 1_{a≠0}|^{p'})^{1/p'}`.

The source states the bound on the gradient of `u_hom` as
`⨍ |∇u_hom|² ≤ |□_m|⁻¹ Σ |∇u 1_{a≠0}|^p`, which is not homogeneous in `u`; the statement here is
the homogeneous form `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²` that the proof gives (Lemma 6.4 (iii) and the
Dirichlet principle). The homogenized solution is the solution of the discrete Dirichlet problem
on the lattice cube; the source takes an `ā`-harmonic function on the continuum cube. The planar
forms are `PlanarMinimalScales`, `PlanarMesoscopicConvergence` and `PlanarHomogenizationError`.
-/

open MeasureTheory LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External
open scoped Matrix

namespace Rigidity.Dirichlet

/-- **Minimal scales of the partition into good cubes** (Armstrong and Dario, Proposition 2.4,
both bounds of (2.13)): for every `t ≥ 1` there is a random scale `𝓜_t ≤ O_s(C)` such that
`3^m ≥ 𝓜_t` implies `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
`size(□_𝒫(x)) ≤ 3^{dm/(d+t)}` for `x ∈ □_m`. -/
def CubeMinimalScales (d : ℕ) (p : unitInterval) : Prop :=
  ∀ t : ℝ, 1 ≤ t → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
    ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ m : ℕ, M ω ≤ 3 ^ m →
        (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
            ((3 : ℝ) ^ (partitionCube ω x).scale) ^ t) / ((3 : ℝ) ^ m) ^ d ≤ C ∧
          ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
            (3 : ℝ) ^ (partitionCube ω x).scale ≤ (3 : ℝ) ^ ((d : ℝ) * m / (d + t))

/-- **Convergence of `μ` and `ν` on the mesoscopic cubes** (Armstrong and Dario, Definition 5.12,
Proposition 5.13 and (6.4)–(6.5), on the triadic cubes of scale `⌈m/8⌉` contained in `□_m`): there
is a random scale `𝒩 ≤ O_s(C)` such that for `3^m ≥ 𝒩`, every such cube `T` and all `q, ξ`,
`|μ(T, q) + (1/2) q · ā⁻¹ q| ≤ C |q|² 3^{-mα}` and `|ν(T, ξ) − (1/2) ξ · ā ξ| ≤ C |ξ|² 3^{-mα}`. -/
def CubeMesoscopicConvergence (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s α C : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧
    ∃ N : Configuration d → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond d p N s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ m : ℕ, N ω ≤ 3 ^ m →
        ∀ T : TriadicCube d, T.scale = (m + 7) / 8 →
          T.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → ∀ q ξ : Fin d → ℝ,
            |cubeMu ω T q + 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i| ≤
                C * (∑ i, q i ^ 2) * (3 : ℝ) ^ (-(α * m)) ∧
              |cubeNu ω T ξ - 1 / 2 * ∑ i, ξ i * (cubeAhom p *ᵥ ξ) i| ≤
                C * (∑ i, ξ i ^ 2) * (3 : ℝ) ^ (-(α * m))

/-- **Armstrong and Dario, Theorem 1, in every dimension, with the discrete homogenized
solution**, for the exponent `p' > 2`: `ā = σ I` with `σ > 0`, and there are `s, α, C > 0` and a
random scale `𝒳 ≤ O_s(C)` such that for `3^m ≥ 𝒳` the partition event holds, `□_m` is resolved
and, for every `u` harmonic on `C_*(□_m)` at the vertices whose lattice neighbours lie in `□_m`,
there is a discrete harmonic `u_hom` on the lattice cube `□_m` with `u_hom = u` on
`C_*(□_m) ∩ ∂□_m`, `|□_m|⁻¹ Σ_{edges in □_m} |∇u_hom|² ≤ C M²` and
`3^{-m} (|□_m|⁻¹ Σ_{C_*(□_m)} (u − u_hom)²)^{1/2} ≤ C 3^{-mα} M`, where `M = cubeGradNorm`. -/
def CubeHomogenizationError (d : ℕ) (p : unitInterval) (p' : ℝ) : Prop :=
  ∃ s α C σ : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧ 0 < σ ∧
    cubeAhom (d := d) p = σ • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ m : ℕ, X ω ≤ 3 ^ m →
        PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ ∧
          ∀ u : Vertex d → ℝ,
            (fun x : ↥(crossingClusterVertices ω ⟨m, 0⟩) => u x) ∈ cubeHarmonic ω ⟨m, 0⟩ →
            ∃ uHom : Vertex d → ℝ,
              (∀ x ∈ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube,
                condLaplacian (constCond fun _ => (1 : ℝ)) uHom x = 0) ∧
              (∀ x ∈ crossingClusterVertices ω ⟨m, 0⟩,
                x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube → uHom x = u x) ∧
              innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
                  uHom / ((3 : ℝ) ^ m) ^ d ≤ C * cubeGradNorm ω m p' u ^ 2 ∧
              (3 : ℝ) ^ (-(m : ℝ)) *
                  √((∑ x ∈ crossingClusterVertices ω ⟨m, 0⟩, (u x - uHom x) ^ 2) /
                    ((3 : ℝ) ^ m) ^ d) ≤
                C * (3 : ℝ) ^ (-(α * m)) * cubeGradNorm ω m p' u

end Rigidity.Dirichlet
