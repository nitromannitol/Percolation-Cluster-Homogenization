# Elliptic regularity and quantitative homogenization on percolation clusters

A machine-checked **Lean 4** formalization of results of the paper

> Scott Armstrong and Paul Dario,
> [*Elliptic regularity and quantitative homogenization on percolation clusters*](https://arxiv.org/abs/1609.09431),
> Communications on Pure and Applied Mathematics 71(9) (2018), 1717–1849; arXiv:1609.09431.

The numbering is that of the arXiv v2 source. The development is built on
[mathlib](https://github.com/leanprover-community/mathlib4) and on the public library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability). It is used by
[Percolation-Rigidity](https://github.com/nitromannitol/Percolation-Rigidity), the formalization of
Bou-Rabee, Cooperman and Dario, *Rigidity of harmonic functions on the supercritical percolation
cluster*, whose Theorems 2.4 and 2.5 quote Theorem 2 of Armstrong and Dario.

[![CI](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/actions/workflows/comparator.yml)

## What is proved

Each edge of `ℤᵈ`, `d ≥ 2`, is open independently with probability `p ∈ (𝔭_c(d), 1)`, where
`𝔭_c(d)` is the bond percolation threshold; the law is `LatticeProb.Percolation.latticeBondLaw d p`
and the threshold `LatticeProb.Percolation.criticalProbability d`. The conductance of an edge is `1`
if it is open and `0` otherwise. Armstrong and Dario prove that the solutions of the Dirichlet
problem on the infinite cluster homogenize, with an algebraic rate (Theorem 1), and that harmonic
functions on the cluster have a large-scale regularity theory above a random minimal scale with
stretched exponential moments (Theorem 2). The Lean statements carry the regime `2 ≤ d`,
`criticalProbability d < p`, `p < 1` as hypotheses; a hypothesis beyond the regime is named in the
table.

| Armstrong and Dario | Lean declaration | Form |
| --- | --- | --- |
| Theorem 1 | `Rigidity.Dirichlet.planarHomogenizationError_holds`, `Rigidity.Dirichlet.cubeHomogenizationError_holds` | `d = 2` for the planar partition, and every `d ≥ 2` for the partition into good cubes; every exponent `p' > 2`; the homogenized matrix is `σ I`, `σ > 0` |
| Theorem 2 (iii), `k = 0` | `Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds`, `Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds` | `d = 2`, and every `d ≥ 2` (the input `LatticeProb.External.ArmstrongDarioOrderZero`) |
| Theorem 2 (iii), `k = 1` | `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_correctorSublinear`, `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` | at the origin, every `d ≥ 2`, from the sublinearity (1.18) of the correctors (Theorem 2 (ii) at `k = 1`) alone, Lemma 7.3 at `k = 2` being proved; or from Lemma 7.3 at `k = 2` and the corrector estimates |
| Theorem 2 (ii), `k = 1` | `Rigidity.Proofs.Regularity.GeneralDim.correctedPlaneExistence_of_sublinearL2Ae`, `Rigidity.Proofs.Regularity.GeneralDim.correctorSublinearL2Ae_of_affineApproximationAe` | every `d ≥ 2`: every slope has a corrected plane (sublinear in the uniform norm) from (1.18) with an almost surely finite scale, and (1.18) from the approximation of affine functions on growing balls (`CubeAffineApproximationAe`) |
| Lemma 7.1 | `Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_holds`, `Rigidity.Proofs.Regularity.cubeHarmonicApproximation_holds` | `d = 2` for the planar partition, and every `d ≥ 2` for the partition into good cubes |
| Lemma 7.2 | `Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2` | every `d` and `k`, from its excess-decay and approximation hypotheses |
| Lemma 7.3 | `Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwo_holds`, `Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates` | `k = 2`, every `d ≥ 2` for the partition into good cubes, with no hypothesis (`ArmstrongDarioMesoscopicDegreeTwo`); `d = 2` for the planar partition |
| Proposition 2.1 | `Rigidity.Percolation.partition_estimates` | every `d`: the partition into good cubes and its moments |
| Proposition 2.4 | `Rigidity.Percolation.exists_minimalScale` | every `d` |
| Propositions 3.4, 3.8 | `Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero`, `Rigidity.Proofs.Cluster.GeneralDim.meyersPartition_holds` | every `d`: the Sobolev inequality and the Meyers estimate on the cluster |
| Propositions 4.9, 4.10 | `Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le`, `Rigidity.Percolation.exists_cubeMuLoc_localization` | every `d` |
| Proposition 5.2 | `Rigidity.Proofs.Cluster.planarMuLimit_eq`, `Rigidity.Proofs.Regularity.planarNuSubaddOsTwo_holds`; `Rigidity.Percolation.cubeMuLimit_eq`, `Rigidity.Percolation.exists_cubeSubaddErr_isOsBond` | `d = 2`; every `d`, (5.2) and (5.3) in the `O_s` form with `s = 1/(2d − 1)` |
| Lemma 5.7 | `Rigidity.Percolation.exists_lintegral_cubeMuGradAvg_sub_le` | every `d`, every triadic cube |
| Lemma 5.9 | `Rigidity.Percolation.exists_cubeOmegaD_le_decay` | every `d`, with the exponent `1/4` |
| Lemmas 5.10, 5.11, Proposition 5.13 | `Rigidity.Percolation.exists_abs_cubeAhomInvLimit_sub_le_pow`, `Rigidity.Percolation.cubeAhomInvLimit_eq`, `Rigidity.Percolation.exists_cubeOmega_isOsBond`, `Rigidity.Percolation.exists_cubeBoundN` | every `d` |
| Proposition 6.1, Lemmas 6.2 and 6.3 | `Rigidity.Dirichlet.cube_sum_sq_sub_uhom_le`, `Rigidity.Dirichlet.cube_lemmaSixTwo`, `Rigidity.Dirichlet.cube_lemmaSixThree`, `Rigidity.Dirichlet.cube_error_chain` | every `d ≥ 2`, on the cluster of the partition into good cubes |
| Proposition A.2 | `Rigidity.Proofs.Multiscale.multiscalePoincare_holds` | every `d` |

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every numbered result of the paper to its Lean
declarations and lists, part by part, where the Lean proofs depart from the paper. The percolation
results that the proofs use are proved too: the concentration of the density of the infinite
cluster in triadic cubes (Dario and Gu, Proposition A.1), slab connectivity above the critical point
for `d ≥ 3`, well-connected cubes for `d ≥ 3`, and planar crossing estimates. The declarations keep the
names (in the namespaces `Rigidity.*`) under which Percolation-Rigidity uses them.

## Literature statements

The statements quoted from the literature are in
[`PercolationClusterHomogenization/External/`](PercolationClusterHomogenization/External/), as
propositions that a theorem takes as an explicit hypothesis when its proof uses them: the
well-connectedness of cubes, the rectangle crossings of Kesten (*Percolation Theory for
Mathematicians*, Theorem 11.1), the concentration of the density of the infinite cluster (Dario and
Gu, Proposition A.1, which is also proved, as `Rigidity.Proofs.S2.cluster_density_concentration`),
the corrector estimate of Dario and Gu (Proposition 2.12) and Theorem 2 (iii) of Armstrong and
Dario in the forms in which Percolation-Rigidity quotes them. The form of Theorem 2 (iii) at `k = 0` in every
dimension, `LatticeProb.External.ArmstrongDarioOrderZero`, is also proved, as
`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`. The theorems of the table above take
none of them unless the table says so.

## Guarantees

- No `sorry`, no `axiom` declarations, no `native_decide`; every listed result depends only on
  `propext`, `Classical.choice` and `Quot.sound`, checked by [`Audit/Axioms.lean`](Audit/Axioms.lean)
  and [`scripts/check_axioms.py`](scripts/check_axioms.py) in CI.
- The library is compiled with `warningAsError`.
- **Independent check of a statement.** Theorem 2 (iii) at `k = 0` is restated using mathlib alone in
  [`HomogenizationAudit/OrderZero/`](HomogenizationAudit/OrderZero/). `Challenge.lean` restates every
  definition that the statement unfolds to, `Solution.lean` proves the restatement from
  `Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only `propext`, `Classical.choice` and `Quot.sound` are used, and replays the proof
  through the Lean kernel and the independent kernel nanoda. The other results have no comparator
  pair.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (Lean `v4.32.0`), mathlib at `81a5d257c8` and Lattice-Probability
at `7512f4fb`.

```bash
lake exe cache get        # mathlib oleans
lake build                # the library, with zero warnings
lake env lean Audit/Axioms.lean 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log
```

## Running the comparator

The pair has a configuration [`HomogenizationAudit/OrderZero/comparator.json`](HomogenizationAudit/OrderZero/comparator.json),
which permits exactly `propext`, `Classical.choice` and `Quot.sound` and enables nanoda. Build
`leanprover/comparator`, `lean4export`, `landrun` and `nanoda` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the repository
root

```bash
COMPARATOR_BIN=<comparator> COMPARATOR_LANDRUN=<landrun> \
COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  ./scripts/run_comparators.sh
```

The script builds the library and, in a fresh copy of the source tree, the audit modules, runs the
comparator on every pair under `HomogenizationAudit/` and fails if a pair is missing or rejected;
its logs are kept under `.lake/comparator-logs/`. The **Comparator audit** workflow runs it when
started manually from the [Actions page](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/actions).

To use the library from another Lake project:

```lean
require «percolation-cluster-homogenization» from git
  "https://github.com/nitromannitol/Percolation-Cluster-Homogenization.git" @ "<commit>"
```

## Repository layout

| Path | Content |
| --- | --- |
| `PercolationClusterHomogenization/Proofs/Partition/` | Section 2: good cubes, the partition, minimal scales |
| `PercolationClusterHomogenization/Proofs/Cluster/` | Sections 3 to 5: coarsening, Sobolev, Caccioppoli, reverse Hölder, Gehring and Meyers on the cluster; the subadditive quantities in every dimension and the planar convergence |
| `PercolationClusterHomogenization/Proofs/Percolation/` | Sections 4 and 5 for `d = 2` (`Planar*`) and in every dimension (`GeneralDim/`); planar percolation geometry |
| `PercolationClusterHomogenization/Proofs/Dirichlet/` | Section 6 and Theorem 1 |
| `PercolationClusterHomogenization/Proofs/Regularity/` | Section 7 and Theorem 2 |
| `PercolationClusterHomogenization/Proofs/Multiscale/` | Appendix A, Proposition A.2 |
| `PercolationClusterHomogenization/Proofs/Density/` | the concentration of the density of the infinite cluster |
| `PercolationClusterHomogenization/Proofs/Lattice/`, `Proofs/Planar/` | symmetries and cubes of the lattice, planar crossings and winding numbers |
| `PercolationClusterHomogenization/Percolation/` | well-connected cubes, slab connectivity and triadic localization |
| `PercolationClusterHomogenization/External/` | the literature statements |
| `PercolationClusterHomogenization/Vendor/` | copied modules (below) |
| `Audit/Axioms.lean`, `scripts/` | the axiom report and its check, and the comparator runner |
| `HomogenizationAudit/` | the mathlib-only comparator pair of Theorem 2 (iii) at `k = 0` |

## How this was built

The Lean code was written with AI coding agents under the direction of Ahmed Bou-Rabee. Every proof
is checked by the Lean kernel.

## Copied code

Some modules are copied from other repositories, with attribution, and not through a Lake
dependency. Each copied file starts with a header naming its source repository, file and commit.

| Source | Commit | Files in this repository |
| --- | --- | --- |
| [anthropics/formal-math](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation), the `percolation/` project (Apache License 2.0; its `LICENSE` and `NOTICE` are kept verbatim in [`PercolationClusterHomogenization/Vendor/FormalMathPercolation/`](PercolationClusterHomogenization/Vendor/FormalMathPercolation/)) | `795efb86f191735c5481675763537cfb4ff37e55` | the 53 modules under `PercolationClusterHomogenization/Vendor/FormalMathPercolation/`, from the files of the same paths under `percolation/Percolation/` |
| [openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) (Apache License 2.0; text in [`PercolationClusterHomogenization/Vendor/CriticalPercolation/LICENSE`](PercolationClusterHomogenization/Vendor/CriticalPercolation/LICENSE)) | `4eaee87548250b2682affda7d05d947c05554bae` | the 44 modules under `PercolationClusterHomogenization/Vendor/CriticalPercolation/`, from `lean/OAI/Probability/CriticalPercolation/` |
| Leonardo Bonanno, [lean-formalizations](https://github.com/leobon12/lean-formalizations/tree/31e748330ee154d5f41537c4b01f71b8a5510c2d) (no licence stated upstream) | `31e748330ee154d5f41537c4b01f71b8a5510c2d` | `PercolationClusterHomogenization/Vendor/BonannoPerc/`: `Basic`, `Duality`, `DualityMain`, `Exclusive`, `ExclusiveMain`, `Paths`, `Peierls`, `StepSum`, from the files of the same names in `LQGMetric/Perc/` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/a6fae9f9df6a47c15e338b928807feb20d9da4b0) (Apache License 2.0) | `a6fae9f9df6a47c15e338b928807feb20d9da4b0` | `PercolationClusterHomogenization/Proofs/Percolation/Kesten/`: `EdgeCrossing`, `DualDecayRectangle`, `RigidityCrossingAdapter` |
| Lattice-High-Contrast-Homogenization (Apache License 2.0, text in [`PercolationClusterHomogenization/Vendor/LHCH/LICENSE`](PercolationClusterHomogenization/Vendor/LHCH/LICENSE)) | `f47a932a9f7a07e1692bfe4aae564d02e8ca0944` | the 48 modules under `PercolationClusterHomogenization/Vendor/LHCH/`, from the files of the same paths under `LatticeHC/`; [`PercolationClusterHomogenization/Proofs/Cluster/SobolevCubePoincare.lean`](PercolationClusterHomogenization/Proofs/Cluster/SobolevCubePoincare.lean), adapted from `LatticeHC/Support/Analysis/CubePoincare.lean` (squares replaced by `p`-th powers) |

The repository of Leonardo Bonanno does not state a licence, and none is claimed here for the
modules copied from it.

## Authors and citation

The paper is by **Scott Armstrong** and **Paul Dario**. The Lean development is by **Ahmed
Bou-Rabee**. It is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The
copied modules listed in [Copied code](#copied-code) keep the terms of their sources.
