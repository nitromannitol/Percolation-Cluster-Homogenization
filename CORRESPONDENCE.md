# Correspondence with Armstrong and Dario

This file maps the numbered results of

> Scott Armstrong and Paul Dario, *Elliptic regularity and quantitative homogenization on percolation
> clusters*, Communications on Pure and Applied Mathematics 71(9) (2018), 1717–1849;
> [arXiv:1609.09431](https://arxiv.org/abs/1609.09431)

to the declarations of this library, and records where the Lean proofs depart from the paper. The
numbering is that of the arXiv v2 source. "AD" below is this paper. Proposition 2.3, Proposition 2.6,
Theorem 1.3, Theorem 2.4, Theorem 2.5 and Theorem 6.5, when not attributed to AD, are those of
Bou-Rabee, Cooperman and Dario, *Rigidity of harmonic functions on the supercritical percolation
cluster* (Trans. Amer. Math. Soc. 378 (2025); arXiv:2303.04736), whose formalization
[Percolation-Rigidity](https://github.com/nitromannitol/Percolation-Rigidity) uses this library;
Proposition 2.3 there is the statement that cubes are well-connected with stretched exponential
probability, and Theorems 2.4 and 2.5 quote Theorem 2 of AD. "Dario and Gu" is *Quantitative
homogenization of the parabolic and elliptic Green's functions on percolation clusters* (Ann.
Probab. 49 (2021); arXiv:1909.10439v4), and "Dario" is *Optimal corrector estimates on percolation
clusters* (Ann. Appl. Probab. 31 (2021), 377–431; arXiv:1805.00902). Their results other than the
concentration of the density of the infinite cluster (Dario and Gu, Proposition A.1) are formalized
in Percolation-Rigidity, and Theorem 2 (iii) at `k = 1` in dimension two from Theorem 1 of Dario
(`armstrongDarioOrderOneOriginTwo_of_dario`) is proved there.

Throughout, `d ≥ 2`, each edge of `ℤᵈ` is open independently with probability `p ∈ (𝔭_c(d), 1)`,
the law is `LatticeProb.Percolation.latticeBondLaw d p`, and the literature inputs enter as
explicit hypotheses (see [`PercolationClusterHomogenization/External/`](PercolationClusterHomogenization/External/)).
Every declaration listed depends only on `propext`, `Classical.choice` and `Quot.sound`; the report
is [`Audit/Axioms.lean`](Audit/Axioms.lean).

## Numbered results

| AD | Lean declaration | Form |
| --- | --- | --- |
| Theorem 1 | `Rigidity.Dirichlet.planarHomogenizationError_holds` | `d = 2`, every exponent `p' > 2`, no hypothesis; the homogenized matrix is `σ I` |
| Theorem 2 (iii), `k = 0` | `Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds` | `d = 2`, no hypothesis |
| Theorem 2 (iii), `k = 1` | `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` | at the origin, every `d`, from Lemma 7.3 at `k = 2` and the corrector inputs |
| Theorem 2 (ii), `k = 1` | `Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_sublinearL2Ae` | `d = 2`, the corrected planes from the sublinearity (1.18) |
| Proposition 2.1 | `Rigidity.Percolation.partition_estimates`, `Rigidity.Percolation.partition_estimates_general` | every `d`; the partition into good cubes, and for any family of good cubes with stretched exponential failure bounds |
| Proposition 2.4 | `Rigidity.Percolation.exists_minimalScale`, `Rigidity.Percolation.exists_minimalScale_general`, `Rigidity.Proofs.Cluster.exists_planar_minimalScale`, `Rigidity.Proofs.Cluster.planarMinimalScales_holds` | every `d`, and for the planar partition |
| Lemma 2.7 | `Rigidity.Percolation.exists_measure_not_mem_goodCubes_le` | every `d` |
| Lemma 2.8 | `Rigidity.Percolation.TriadicCube.reachable_of_mem_goodCubes` | every `d` |
| Corollary 2.10 | `Rigidity.Percolation.reachable_partitionAnchor_of_walk` | every `d` |
| Lemma 3.2 | `Rigidity.Percolation.partition_sum_abs_sub_coarseAnchor_rpow_le` | every `d`, on cubes resolved by the partition, with the reach weight |
| Lemma 3.3 | `Rigidity.Percolation.partition_sum_gradNormIn_coarseAnchor_rpow_le` | every `d`, on resolved cubes |
| Proposition 3.4 | `Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero` and the two variants of the same file and of `SobolevCoarseZero.lean`, `Rigidity.Percolation.exists_clusterSobolevTwo` | every `d`, `s ≥ d/(d − 1)`, three of the four boundary conditions |
| Lemma 3.5 | `Rigidity.Proofs.Cluster.caccioppoli_cluster` | every `d` |
| Lemma 3.6 | `Rigidity.Proofs.Cluster.reverse_holder_partition_cube` | every `d`, deterministic part; the probability bound through the reverse Hölder cubes (Section 3 below) |
| Definition 3.7, Proposition 3.8 | `Rigidity.Proofs.Cluster.meyers_cluster`, `Rigidity.Proofs.Cluster.planar_meyers_rh_uniform` | deterministic part in every `d`; above the partition `𝓡` in every `d` and in `d = 2` |
| Definition 3.9 | `Rigidity.Proofs.Cluster.GeneralDim.meyersPartition_holds` | every `d` |
| Definition 4.1 | `Rigidity.Percolation.cubeMu`, `Rigidity.Percolation.cubeNu` | every `d` (`planarMu`, `planarNu` in the planar modules) |
| Lemma 4.2 | `Rigidity.Percolation.sum_clusterForm_sub_add_sum_planarMu_subcubes_le` | `d = 2`; every `d` in `Proofs/Percolation/GeneralDim/` |
| Corollary 4.6 | `Rigidity.Percolation.sum_mul_le_neg_cubeMu_add_cubeNu` | every `d`, with its face errors |
| Proposition 4.9 | `Rigidity.Percolation.exists_measure_planarCappedDiscrepancy_le`, `Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le` | `d = 2` and every `d` |
| Proposition 4.10 | `Rigidity.Percolation.exists_planarNuLoc_localization`, `Rigidity.Percolation.exists_planarMuLoc_localization`, `Rigidity.Percolation.exists_cubeMuLoc_localization` | `d = 2`; every `d` for `μ` (for `ν`, locality holds by definition) |
| Definition 5.1, (5.1) | `Rigidity.Percolation.planarNuLimit_eq_planarAhom`, `Rigidity.Percolation.exists_planarAhom_bounds`, `Rigidity.Percolation.cubeAhom` | `d = 2` and every `d` |
| Proposition 5.2 | `Rigidity.Proofs.Cluster.planarMuLimit_eq`, `Rigidity.Proofs.Regularity.planarNuSubaddOsTwo_holds`; `Rigidity.Percolation.exists_cubeSubaddErr_isOsBond_of_decay` | `d = 2`: the qualitative part, the rate, and the `O_s` form; every `d`: (5.2) and (5.3) in the `O_s` form with `s = 1/(2d − 1)`, given the bound of Lemma 5.9 |
| Lemma 5.4 | `Rigidity.Percolation.exists_lintegral_planarMuDefect_le` | `d = 2`; every `d` in `GeneralMuEnergyDefect.lean` |
| Lemma 5.5 | `Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenMu_holds`, `Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenNu_holds`; `Rigidity.Percolation.exists_lintegral_cubeMuRestrictError_le`, `Rigidity.Percolation.exists_lintegral_cubeNuRestrictError_le` | `d = 2`; every `d`, for `□_m` and `2d ≤ n < m ≤ 2n`, `ν` at the slopes `ā⁻¹ q` |
| Lemma 5.7 | `Rigidity.Proofs.Cluster.planarWeakConvergence_holds`; `Rigidity.Percolation.exists_lintegral_cubeMuGradAvg_sub_le` | `d = 2`; every `d`, for every triadic cube |
| Lemma 5.9 | `Rigidity.Proofs.Cluster.exists_planarOmegaD_decay_holds` | `d = 2` |
| Lemma 5.10 | `Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration`, `Rigidity.Percolation.exists_planarOmegaD_le_pow_of_decay`, `Rigidity.Percolation.exists_cubeOmegaD_le_pow_of_decay` | for real sequences, for `D_n` in `d = 2`, and in every `d` given the bound of Lemma 5.9 |
| Lemma 5.11 | `Rigidity.Percolation.exists_cubeOmega_isOsBond_of_decay` | every `d`, in the `O_s` form with `s = 1/(2d − 1)`, given the bound of Lemma 5.9 |
| Definition 5.12, Proposition 5.13 | `Rigidity.Percolation.exists_cubeBoundN_of_decay` | every `d`, given the bound of Lemma 5.9 |
| Proposition 6.1, Lemmas 6.2 to 6.4 | `Rigidity.Dirichlet.sum_sq_sub_le_of_inner_energy_chain`, `Rigidity.Dirichlet.innerEdgeEnergy_dirichletSolution_div_le_of_coarse` | every `d`, deterministic steps on the lattice |
| Lemma 7.1 | `Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_holds` | `d = 2`, no hypothesis |
| Lemma 7.2 | `Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2` | every `k`, with its excess-decay and approximation hypotheses |
| Lemma 7.3 | `Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_zero_planar`, `Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_one_planar`, `Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates` | `d = 2`, `k = 0, 1, 2` |
| Proposition A.2 | `Rigidity.Proofs.Multiscale.multiscalePoincare_holds`, `Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine` | every `d` |

The percolation results that these proofs use are proved as well: the concentration of the density
of the infinite cluster in triadic cubes (Dario and Gu, Proposition A.1;
`Rigidity.Proofs.S2.cluster_density_concentration` in every dimension and
`Rigidity.Proofs.S2.planar_cluster_density_concentration` for `d = 2`), slab connectivity above the
critical point for `d ≥ 3` (Grimmett and Marstrand), well-connected cubes for `d ≥ 3` and their
reduction to `d = 2`, the finite clusters for `d ≥ 3`, and the planar crossing estimates. The
sections below describe each part, with its departures from the paper.

## Slab connectivity above the critical point

For `d ≥ 3`, the theorem of Grimmett and Marstrand (G. R. Grimmett and J. M. Marstrand, *The
supercritical phase of percolation is well behaved*, Proc. R. Soc. Lond. A 430 (1990), 439–457;
Grimmett, Chapter 7) is proved for bond percolation, in the finite-volume form that the coarse
graining uses.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`](PercolationClusterHomogenization/Percolation/Blocks/SlabConnectivity.lean) | If `3 ≤ d` and `criticalProbability d < p`, then `UniformCubeSlabConnectivity d p`. |

The proposition `UniformCubeSlabConnectivity d p`, defined in
[`PercolationClusterHomogenization/Percolation/SlabTriadicPartition.lean`](PercolationClusterHomogenization/Percolation/SlabTriadicPartition.lean),
states that there are a width `w ≥ 1` and a constant `ρ > 0` such that for every cube
`U = c + [0, n)ᵈ`, every direction `a` and every `k` with `(k + 1) w ≤ n`, any two vertices of the
slab `{x ∈ U : c_a + k w ≤ x_a < c_a + (k + 1) w}` are joined by an open path inside the slab with
probability at least `ρ`. The theorem depends on exactly `propext`, `Classical.choice` and
`Quot.sound`, and its axiom report is checked with those of the numbered results. The same file
derives from this bound the triadic stopping partition with its exponential size moment and its
localization bound
(`Rigidity.Percolation.triadic_partition_estimates_of_uniformCubeSlabConnectivity`), and the next
section derives from it Proposition 2.3 for `d ≥ 3`.

Steps 1 to 3 below follow Chapter 2 of D. Contreras, *Percolation on graphs of polynomial growth*,
ETH Zürich dissertation (2022), doi:10.3929/ethz-b-000585148, which proves the theorem of Grimmett
and Marstrand by a bootstrap. Step 4 is the route of the Lean proof from the bootstrap to slabs, a
static renormalization in slabs. The files are in
[`PercolationClusterHomogenization/Percolation/Bootstrap/`](PercolationClusterHomogenization/Percolation/Bootstrap/) and
[`PercolationClusterHomogenization/Percolation/Blocks/`](PercolationClusterHomogenization/Percolation/Blocks/).

1. **Local inputs** (`Bootstrap/LocalInputs.lean`), from the formal-math library (see
   [Copied code](README.md#copied-code)): the uniqueness zone and the fact that large finite sets meet the
   infinite cluster (S. Martineau and V. Tassion, *Locality of percolation for abelian Cayley
   graphs*, Ann. Probab. 45 (2017), proof of Lemma 3.7 and Lemma 3.6), and the connection of a large
   cube to each face orthant of a larger cube (Grimmett, (7.14)–(7.16)).
2. **Seeds and sprinkling** (dissertation, Lemmas 2.3.2–2.3.5): a seed is joined to each face
   orthant of a large cube (`Bootstrap/SeedFaceLink.lean`); connection estimates compose by
   sprinkling (`Bootstrap/SprinkledExit.lean`, `Bootstrap/Composition.lean`); and a left seed of
   scale `3m'` reaches the anchors of the two subregions of scale `m'` (`Bootstrap/Relay.lean`,
   `Bootstrap/AnchorReach.lean`).
3. **Bootstrap** (dissertation, Theorem 2.1.2): above `𝔭_c(d)`, for every `ε > 0` there is a seed
   radius such that at arbitrarily large scales `m` every left seed and every right seed of scale
   `m` are joined inside `Q_{6m}` with probability at least `1 − ε`
   (`Rigidity.Percolation.exists_seed_link`, `Bootstrap/Link.lean`). The step from scale `m'` to
   scale `3m'` is `Bootstrap/Recursion.lean`, and its iteration `Bootstrap/Iteration.lean`.
4. **Static renormalization.** In a slab box with two long sides and thin sides `12m + 1`, blocks
   centred on a square grid of mesh `10m` are good when the uniqueness zone holds at the centre and
   the block is linked to its four neighbours (`Blocks/LinkEvents.lean`, `Blocks/SlabBlocks.lean`).
   The good blocks form a dependent site percolation of finite range and high density on a
   rectangle of `ℤ²`. The Peierls bound for such percolation, from Leonardo Bonanno's library (see
   [Copied code](README.md#copied-code)), and a recursion over quadrants join any two vertices of the slab
   box with probability bounded below, uniformly in the size of the box
   (`Blocks/GridPeierls.lean`, `Blocks/SlabTwoPoint.lean`). Two vertices of a slab of a cube are
   joined through `d` intermediate vertices, changing one coordinate at a time inside a slab box,
   by Harris' inequality; small cubes are handled by finite energy (`Blocks/SlabConnectivity.lean`).

**Departure from the dissertation.** The probabilistic step of the bootstrap, Lemma 2.4.1, is proved
in a form with zones (`Bootstrap/TwoChances.lean`). Each of the two seeds lies in a zone of its
region and is conditioned to have its cut inside the zone closed at the level `p₀`. The two clusters
are explored, at the level `p₀` raised to `q = p₀ + δ` on the cut from the seed only, inside two
disjoint regions that meet the two subregions of the smaller scale exactly in their zones, and the
traces of the clusters in these zones are conditioned in the same way as the seeds. The recursion is
over seeds with this conditioning (`BootGood`, `Bootstrap/Recursion.lean`), so the conditioning of
the traces is the conditioning at the smaller scale. The levels `p₀` and `q` are the same at every
scale and each bond is sprinkled at most once, so the number of scales is not restricted.

## Well-connected cubes and finite clusters for d ≥ 3

For `d ≥ 3` and `𝔭_c(d) < p`, slab connectivity gives Proposition 2.3 of the paper and the
exponential decay of the radius of finite clusters (Grimmett, Theorem (8.21), due to J. T. Chayes,
L. Chayes, G. R. Grimmett, H. Kesten and R. H. Schonmann, *The correlation length for the
high-density phase of Bernoulli percolation*, Ann. Probab. 17 (1989), 1277–1302).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.wellConnected_of_three_le`](PercolationClusterHomogenization/Percolation/Pisztora/WellConnected.lean) | If `3 ≤ d` and `criticalProbability d < p`, there are `c, C, s > 0` such that every cube `x + Q_N` fails to be well-connected with probability at most `C exp(−c Nˢ)`: the statement of `WellConnectedInput` at `d`, here with `s = 1/(100d³)` and without the hypothesis `p < 1`. |
| [`Rigidity.Percolation.wellConnectedInput_of_planar`](PercolationClusterHomogenization/Percolation/Pisztora/WellConnected.lean) | The case `d = 2` of `WellConnectedInput` implies `WellConnectedInput`. |
| [`Rigidity.Percolation.exists_finite_cluster_radius_le`](PercolationClusterHomogenization/Percolation/Pisztora/FiniteClusters.lean) | If `3 ≤ d` and `criticalProbability d < p`, the open cluster of `x` is finite and reaches `ℓ^∞`-distance `l` from `x` with probability at most `C exp(−c l)`, for all `x` and `l`. |
| [`Rigidity.Percolation.exists_finite_cluster_card_le`](PercolationClusterHomogenization/Percolation/Pisztora/FiniteClusters.lean) | Under the same hypotheses, the open cluster of `x` is finite with at least `n` vertices with probability at most `C exp(−c n^{1/d})`. |

The four theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Crossing estimate** (`Rigidity.Percolation.crossing_fail_le`, `Pisztora/CubeEstimates.lean`).
   From the slab bound, a cube of side `n` has, for `10dw ≤ r < 10dn`, a crossing component joined
   inside the cube to every open path that leaves each `ℓ¹`-ball of radius `r/10`, except with
   probability at most `(d + 2)(n + 1)^{2d+1} exp(−c(⌊r/(10dw)⌋ − 1))`. The proof explores the
   slabs of the cube one at a time (`PercolationClusterHomogenization/Percolation/SlabRadiusCrossing.lean` and the modules
   it imports).
2. **Good cubes** (`Pisztora/GoodSubcube.lean`, `Pisztora/WellConnected.lean`). In `z + Q_M` take
   `t = ⌊M^{1/d}/(4 · 100^{1/d})⌋` and `r = 8t`. The crossing component is a largest cluster and
   contains every open path with at least `M/100` steps, because every other cluster has fewer than
   `(4t)^d ≤ M/100` vertices. So `z + Q_M` is good and crossing outside an event of probability at
   most `K exp(−κ M^{1/d})` (`Rigidity.Percolation.exists_not_goodSubcube_le`). A union bound over
   the cube `x + Q_N` and the at most `(4N + 1)^d (N + 1)` cubes `z + Q_M` that meet it with
   `N^{1/(10d)²}/2 ≤ M ≤ N/10` gives the statement. This is the derivation stated with the input,
   with Pisztora's box estimate replaced by the crossing estimate.
3. **Finite clusters** (`Pisztora/FiniteClusters.lean`). If `2t < l` and, for every `k`, the cube
   `x + Q_{M_k}`, `M_k = 2^{k+1} t`, has a crossing root joined inside it to every open path of
   coordinate diameter at least `M_k`, then the open path from `x` to distance `l` joins `x` to the
   first root, and a crossing path of the `k`-th cube, of diameter `M_{k+1}`, joins the `k`-th root
   to the next one; the cluster of `x` then meets every face of every cube and is infinite. By the
   crossing estimate the `k`-th condition fails with probability at most `A exp(−κ 2^k t)`, and the
   sum over `k` gives the bound. This route through the crossing estimate departs from the proof of
   Chayes, Chayes, Grimmett, Kesten and Schonmann. The volume bound follows, since a cluster of
   `ℓ^∞`-radius less than `l` has at most `(2l)^d` vertices.

## Proposition 2.3 and the density concentration for d = 2

For `d = 2` and `𝔭_c(2) < p < 1`, Kesten's rectangle-crossing estimate, which is proved (see
[Assumed literature inputs](https://github.com/nitromannitol/Percolation-Rigidity#assumed-literature-inputs)), gives Proposition 2.3 of the paper and
the density concentration of Dario and Gu, Proposition A.1, in the plane. With the theorems of the
previous section, Proposition 2.3 holds in every dimension, and so does Theorem 6.5, with no
literature hypothesis.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.wellConnected_input_two`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Percolation/PlanarWellConnected.lean) | `WellConnectedInputTwo`, the statement of `WellConnectedInput` at `d = 2`, here with `s = 1/800`. |
| [`Rigidity.Percolation.wellConnected_input`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Percolation/WellConnected.lean) | `WellConnectedInput`: Proposition 2.3 for every `d ≥ 2`, from `wellConnected_input_two` and `wellConnected_of_three_le`. |
| [`Rigidity.Proofs.S2.planar_cluster_density_concentration`](PercolationClusterHomogenization/Proofs/Density/PlanarDensityConcentration.lean) | `ClusterDensityConcentrationInputTwo`, the statement of `ClusterDensityConcentrationInput` at `d = 2`: the density of the infinite cluster in a triadic square of side `3ᵐ` differs from `θ(𝔭)` by `O_{2/15}(C 3^{−m})`. |
| [`Rigidity.Assembly.Unconditional.slow_mixing`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Assembly/Unconditional.lean) | Theorem 6.5 for every `d ≥ 2` and `𝔭_c(d) < p < 1`, with no literature hypothesis. |

The four theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Well-connected squares** (`Rigidity/Proofs/Percolation/PlanarGoodCube.lean`,
   `PlanarWellConnected.lean` and the modules they import). In the square `z + Q_M`, `M ≥ 10⁴`, let
   `w = ⌊√M⌋/100`. Outside an event of probability at most a polynomial in `M` times `exp(−c w)`,
   every horizontal and vertical strip of width `w` of the square has an open crossing in its long
   direction, and the square has a unique crossing cluster. The strip crossings then lie in the
   crossing cluster, every other open cluster of the square lies in a square of side `2w + 1`, so
   the crossing cluster is a largest cluster, and every open path with at least `M/100` steps is
   joined to it by a transverse crossing. The square is then good, and the union bound over
   subcubes stated with the input gives the statement with `s = 1/800 = 1/(d(10d)²)`. This route
   replaces the estimate of Couronné and Messikh by Kesten's estimate.
2. **Density concentration** (`Rigidity/Proofs/S2/`, from `BondEfronStein.lean` to
   `PlanarDensityConcentration.lean`). Resampling one bond changes the number of vertices of the
   infinite cluster in the square by at most the sum of the sizes of the finite clusters at the
   endpoints of the bond, before and after resampling. These sizes have stretched-exponential
   tails, because a loop of the infinite cluster in an annulus, obtained from rectangle crossings,
   encloses every finite cluster that meets the inner square (`ClusterDensityInfluenceBound.lean`,
   `PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteCluster.lean`). The Efron–Stein inequality for the
   product of the Bernoulli bonds, applied to the powers of the centred density `X`, gives for
   `n ≥ 2` the recursion
   `E|X|^{2n} ≤ (E|X|ⁿ)² + C n^{14} 3^{−2m} (E|X|^{2n})^{(n−1)/n}`
   (`Rigidity.Proofs.S2.planar_density_moment_recursion`). Solving it bounds the tail of `X` at
   the scale `C 3^{−m}` with the exponent `1/7`, which gives the stated exponent `2/15`. Dario and
   Gu derive the estimate from a concentration inequality of Efron–Stein type beyond the variance;
   the Lean proof replaces it by this iteration of the variance inequality.

## Density concentration in every dimension

For `d ≥ 3` and `𝔭_c(d) < p`, the finite-cluster estimates of
[Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3)
give the density concentration of Dario and Gu, Proposition A.1. With the case `d = 2` of the
previous section, `ClusterDensityConcentrationInput` is proved, and the versions of Proposition 2.6
and Theorem 1.3 in `Rigidity.Assembly.WithProvedDensity` do not take it as a hypothesis.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.S2.cluster_density_concentration`](PercolationClusterHomogenization/Proofs/Density/ClusterDensityConcentration.lean) | `ClusterDensityConcentrationInput`: for `d ≥ 2` and `𝔭_c(d) < p < 1`, the density of the infinite cluster in a triadic cube of side `3ᵐ` differs from `θ(𝔭)` by `O_{2(d−1)/(3d²+2d−1)}(C 3^{−dm/2})`; from `planar_cluster_density_concentration` (`d = 2`) and `clusterDensityConcentrationAt_of_three_le` (`d ≥ 3`, without the hypothesis `p < 1`). |
| [`Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Assembly/ProvedDensity.lean) | Proposition 2.6 for every `d ≥ 2`, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin` and `SupercriticalBondGreenQuantitative`. |
| [`Rigidity.Assembly.WithProvedDensity.fast_decay`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Assembly/ProvedDensity.lean) | Theorem 1.3, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderZero`, `ArmstrongDarioOrderOneOrigin`, `SupercriticalBondGreenColumnExistence` and `SupercriticalBondGreenQuantitative`. |

The three theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Density/`](PercolationClusterHomogenization/Proofs/Density/), from `DensityResamplingEnergy.lean` to
`ClusterDensityConcentration.lean`, and
[`PercolationClusterHomogenization/Proofs/Percolation/BondShellExponential.lean`](PercolationClusterHomogenization/Proofs/Percolation/BondShellExponential.lean).

1. **Influences** (`FiniteClusterVolumeMoments.lean`, `InfluenceRadiusTail.lean`,
   `InfluenceRootBoundHigh.lean`). As in the plane, resampling a bond `e` changes the number of
   vertices of the infinite cluster in the cube by at most the sizes of the finite clusters at the
   endpoints of `e`, before and after resampling, and changes it only if one of these finite
   clusters meets the cube. The volume tail `C exp(−c n^{1/d})` of finite clusters gives the
   moments `E|Δ_e|^r ≤ 4^{r+1} (dr)! a^{−dr} C`. By the radius tail `C exp(−c l)`, a bond at
   coordinate distance `n` from the cube changes the count with probability at most `C exp(−cn)`,
   and by the Cauchy–Schwarz inequality the moments of its influence decay exponentially in `n`.
   Summing over the bond shells around the cube gives
   `Σ_e ‖Δ_e‖²_{L^{2r}} ≤ C r^{3d+2} (3ᵐ + 1)^d`
   (`Rigidity.Proofs.S2.densityInfluenceRootBound_of_three_le`).
2. **Moment recursion** (`DensityResamplingEnergy.lean`, `DensityRealEncoding.lean`,
   `DensityMomentGrowth.lean`, `DensityConcentrationOfRoots.lean`). The argument of the planar case,
   written for every `d` under the hypothesis `DensityInfluenceRootBound d p (2γ)` that this sum is
   at most `C r^{2γ} (3ᵐ + 1)^d`. The Efron–Stein inequality for the powers of the centred density
   `X` gives, for `n ≥ 2`,
   `E|X|^{2n} ≤ (E|X|ⁿ)² + C n^{2γ+2} 3^{−dm} (E|X|^{2n})^{(n−1)/n}`
   (`Rigidity.Proofs.S2.density_moment_recursion`), hence `‖X‖_{Lⁿ} ≤ C n^{γ+1} 3^{−dm/2}` and
   `|X| ≤ O_s(C 3^{−dm/2})` for every `0 < s ≤ 1/(γ + 1)`
   (`Rigidity.Proofs.S2.isOsBond_density_of_rootBound`; at the exponent of the source,
   `Rigidity.Proofs.S2.clusterDensityConcentrationAt_of_rootBound`). For `d ≥ 3` the Lean proof
   takes `γ = ⌊(3d + 3)/2⌋`, so that `2γ ≥ 3d + 2`; since `2(γ + 1) ≤ 3d + 5`, the exponent
   `1/(γ + 1)` is at least `2(d − 1)/(3d² + 2d − 1)` (for `d = 3`, `1/7 ≥ 1/8`).

**Departures from Dario and Gu.** Dario and Gu prove Proposition A.1 with an exponential
Efron–Stein inequality (their Proposition A.3, from S. Armstrong and J. Lin, *Optimal quantitative
estimates in stochastic homogenization for elliptic equations in nondivergence form*, Arch. Ration.
Mech. Anal. 225 (2017), Proposition 2.2) and the volume tail `exp(−c n^{(d−1)/d})` of finite clusters
(their Theorem 6, from H. Kesten and Y. Zhang, *The probability of a large finite cluster in
supercritical Bernoulli percolation*, Ann. Probab. 18 (1990), 537–555). The Lean
proof replaces the exponential inequality by the iteration of the Efron–Stein variance inequality
over the moments, as for `d = 2`. For `d ≥ 3` it replaces the tail of Kesten and Zhang by the
exponential decay of the radius of finite clusters (Grimmett, Theorem (8.21)) and the volume tail
`exp(−c n^{1/d})` that follows from it, both proved from slab connectivity in
[Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3).
It obtains the scale `3^{−dm/2}` of the source with the exponent `1/(⌊(3d + 3)/2⌋ + 1)` for
`d ≥ 3` and `1/7` for `d = 2`, which are at least the exponent `2(d − 1)/(3d² + 2d − 1)` of the
source, and it derives the stated exponent from them. The case `d = 2` is the planar proof of the
previous section. The modules for `d ≥ 3` and every `d` follow the planar modules of the previous
section; no code is copied from another repository.

## Multiscale Poincaré inequality

The proofs of Section 5 of Armstrong and Dario bound a function on a triadic cube by the spatial
averages of its gradient over the subcubes of every intermediate scale (AD, Proposition A.2).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Multiscale.multiscalePoincare_holds`](PercolationClusterHomogenization/Proofs/Multiscale/Poincare.lean) | AD Proposition A.2 (`MultiscalePoincare d`, [`Defs.lean`](PercolationClusterHomogenization/Proofs/Multiscale/Defs.lean)): for every triadic cube `□_m` of `ℤᵈ`, every `n` with `m/2 ≤ n ≤ m` and every `u : ℤᵈ ∩ □_m → ℝ`, `‖u − (u)_{□_m}‖_{L̲²(□_m)} ≤ C 3^n ‖∇u‖_{L̲²(□_m)} + C Σ_{k=n}^{m−1} 3^k (the mean over the subcubes of size 3^k of the squared average of ∇u)^{1/2}` |
| [`Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine`](PercolationClusterHomogenization/Proofs/Multiscale/Affine.lean) | the same inequality for `u − ℓ_ξ`, with `ℓ_ξ(x) = ξ · x`, in the form used for Lemma 5.8 of AD |

The two theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules are
in [`PercolationClusterHomogenization/Proofs/Multiscale/`](PercolationClusterHomogenization/Proofs/Multiscale/).

Departures from Armstrong and Dario:

- **Route.** AD smooth `u` and apply the continuum multiscale Poincaré inequality (their
  Proposition A.1, from Armstrong, Kuusi and Mourrat). The Lean proof extends `u` to the closed
  lattice cube with one more layer by clamping, applies the lattice multiscale Poincaré inequality
  with face-weighted block means `LatticeHC.exists_sum_sq_sub_vertexMean_le_multiscale` (see
  [Copied code](README.md#copied-code)), and compares the block means with the subcube averages: the boundary
  layer contributes at most `C 3^{m/2}` times the gradient norm, which is at most `C 3^n` times it
  since `n ≥ m/2`.
- **Normalization.** The gradient sums count each edge once; AD's inner product counts both
  orientations, which changes only the constant.
- **Affine form.** The averages of `∇u` are compared with `(1 − 3^{−k}) ξ`, the exact average of the
  gradient of `ℓ_ξ` over a subcube, where AD write `ξ`; the difference adds at most `(m − n)|ξ|` to
  the right side.

## Partitions into good cubes and functional inequalities on the cluster

The proof of Theorem 2 of AD, from which Theorems 2.4 and 2.5 are quoted, starts from a random
partition of `ℤᵈ` into good triadic cubes (AD, §2) and from functional and elliptic inequalities on
the cluster above the scale of this partition (AD, §3). For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the
partition and its stochastic integrability are proved, and so are the deterministic parts of the
inequalities of §3, with the Sobolev inequality on the cluster (AD, Proposition 3.4) for
`s ≥ d/(d − 1)` in three of its four cases.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.partition_estimates`](PercolationClusterHomogenization/Proofs/Partition/AlmostSure.lean) | AD Proposition 2.1 for the good cubes: almost surely every vertex lies in exactly one maximal stopping cube `□_𝒫(x)` of the partition `𝒫`, `E[exp(size(□_𝒫(x))/θ)] ≤ 2` for every vertex `x`, and the partition is approximately local. |
| [`Rigidity.Percolation.partition_estimates_general`](PercolationClusterHomogenization/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.1 for any random collection of good cubes whose failure probabilities are at most `C exp(−c 3^{ns})`, with `E[exp((size/θ)^s)] ≤ 2`. |
| [`Rigidity.Percolation.exists_minimalScale`](PercolationClusterHomogenization/Proofs/Partition/MinimalScaleCombined.lean) | AD Proposition 2.4 for `𝒫`: for every `t ∈ ℕ` there are `C` and a measurable random scale `M`, finite almost surely, with a stretched exponential moment such that, almost surely, `M < 3ᵐ` implies `Λ_t(□_m) ≤ C` and that every vertex of `□_m` lies in a partition cube of size at most `3^{dm/(d+t)}`. |
| [`Rigidity.Percolation.exists_minimalScale_general`](PercolationClusterHomogenization/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.4 for a random collection of good cubes satisfying AD (2.1) and (2.2) with `0 < s ≤ 1`. |
| [`Rigidity.Percolation.exists_measure_not_mem_goodCubes_le`](PercolationClusterHomogenization/Proofs/Partition/AlmostSure.lean) | AD Lemma 2.7: a triadic cube of scale `n` fails to be good with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.TriadicCube.reachable_of_mem_goodCubes`](PercolationClusterHomogenization/Proofs/Partition/Adjacent.lean) | AD Lemma 2.8: the crossing clusters of two good cubes containing lattice neighbours, whose scales are equal or differ by one, are joined by an open path inside the union of the two cubes. |
| [`Rigidity.Percolation.reachable_partitionAnchor_of_walk`](PercolationClusterHomogenization/Proofs/Partition/Paths.lean) | AD Corollary 2.10: along every lattice walk from `x` to `y`, the anchors of `□_𝒫(x)` and `□_𝒫(y)` are joined by an open path inside the union of the partition cubes of the vertices of the walk. |
| [`Rigidity.Percolation.partition_sum_abs_sub_coarseAnchor_rpow_le`](PercolationClusterHomogenization/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.2 on a triadic cube `U` resolved by the partition, for `1 ≤ s < ∞`: `Σ_{x ∈ C_*(U)} \|w(x) − [w]_𝒫(x)\|^s ≤ C^s Σ_{z ∈ C_*(U)} 3^{sdρ(z)} \|∇w 1_{𝐚≠0}\|^s(z)`, with `ρ(z) ≥ scale(□_𝒫(z))` the reach scale. |
| [`Rigidity.Percolation.partition_sum_gradNormIn_coarseAnchor_rpow_le`](PercolationClusterHomogenization/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.3 on a resolved cube `U`, for `1 ≤ s < ∞`: `Σ_{x ∈ U} \|∇[w]_𝒫\|^s(x) ≤ C^s Σ_{z ∈ C_*(U)} size(□_𝒫(z))^{sd−1} \|∇w 1_{𝐚≠0}\|^s(z)`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_latticeSobolevOn`](PercolationClusterHomogenization/Proofs/Cluster/PartitionSobolev.lean) | AD Proposition 3.4 on a resolved cube `U`, for `1 ≤ t ≤ s` and `w` of mean zero on `C_*(U)`, given the Sobolev inequality `Σ_U \|f − (f)_U\|^s ≤ S (Σ_U \|∇f\|^t)^{s/t}` of the lattice cube: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_sq_le_two`](PercolationClusterHomogenization/Proofs/Cluster/PartitionSobolevTwo.lean) | AD Proposition 3.4 for `d = 2`, `s = 2` and `t = 1`, the Sobolev inequality of the planar lattice square being proved. |
| [`Rigidity.Percolation.IntegerCube.exists_latticeSobolevOn`](PercolationClusterHomogenization/Proofs/Cluster/SobolevCube.lean) | the Sobolev–Poincaré inequality of the integer cubes of `ℤᵈ`, `d ≥ 2`: for `s ≥ d/(d − 1)` and `t = sd/(s + d)` there is `S` with `Σ_B \|f − (f)_B\|^s ≤ S (Σ_B \|∇f\|^t)^{s/t}` on every cube `B`. |
| [`Rigidity.Percolation.exists_sum_rpow_le_of_eq_zero_on_boundary`](PercolationClusterHomogenization/Proofs/Cluster/SobolevZero.lean) | the Sobolev inequality with zero boundary values: `Σ_D \|f\|^s ≤ S (Σ_D \|∇f\|^t)^{s/t}` for every finite `D ⊆ ℤᵈ` and every `f` vanishing at the points of `D` with a lattice neighbour outside `D`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero`](PercolationClusterHomogenization/Proofs/Cluster/SobolevPartition.lean) | AD Proposition 3.4 on a resolved cube `U`, `d ≥ 2`, `s ≥ d/(d − 1)`, for `Σ_{C_*(U)} w = 0`: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_coarsen_eq_zero`](PercolationClusterHomogenization/Proofs/Cluster/SobolevPartition.lean) | the same for `Σ_U [w]_𝒫 = 0`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_coarsen_eq_zero`](PercolationClusterHomogenization/Proofs/Cluster/SobolevCoarseZero.lean) | the same for `[w]_𝒫 = 0` at the points of `U` with a lattice neighbour outside `U`. |
| [`Rigidity.Percolation.exists_clusterSobolevTwo`](PercolationClusterHomogenization/Proofs/Cluster/SobolevReverseHolder.lean) | AD Proposition 3.4 with `s = 2` in the form of the Sobolev hypothesis `ClusterSobolevTwo` of the reverse Hölder inequality, on `C_*(U)` for every resolved cube `U`, `d ≥ 2`. |
| [`Rigidity.Proofs.Cluster.caccioppoli_cluster`](PercolationClusterHomogenization/Proofs/Cluster/Caccioppoli.lean) | AD Lemma 3.5: if `V ⊆ U`, every point of `U` with an open edge leaving `U` is at `ℓ∞` distance at least `r > 0` from `V`, and `u` is harmonic at the points of `U` all of whose open edges stay in `U`, then `Σ_V \|∇u 1_{𝐚≠0}\|² ≤ (8d/r²) Σ_{U ∖ int V} u²`. |
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube`](PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderPartition.lean) | AD Lemma 3.6, deterministic part: on the crossing cluster of a resolved triadic cube `□` of scale `m + 1`, given the Sobolev inequality of the lattice cube with exponents `2` and `2_* = 2d/(d+2)` and `Σ_{C_*(□)} 3^{2dsρ} ≤ C_G \|□\|`, every `u` harmonic on `C_*(□)` has `3^{−md} Σ_{C_*(□) ∩ □'} \|∇u\|² ≤ C (\|□\|⁻¹ Σ_{C_*(□)} \|∇u\|^{t2_*})^{2/(t2_*)}`, `□'` the central subcube and `1/s + 1/t = 1`. |
| [`Rigidity.Proofs.Cluster.gehring_triadic`](PercolationClusterHomogenization/Proofs/Cluster/Gehring.lean) | Gehring's lemma on the triadic cubes of `ℤᵈ`: for `0 < θ < 1`, a reverse Hölder inequality `avg_Q g ≤ A (avg_{Q^j} g^θ)^{1/θ}` on every subcube `Q` of `□` whose enlargement `Q^j` lies in `3□` gives `ε > 0` with `avg_□ g^{1+ε} ≤ C (avg_{3□} g)^{1+ε}`. |
| [`Rigidity.Proofs.Cluster.meyers_cluster`](PercolationClusterHomogenization/Proofs/Cluster/MeyersCluster.lean) | AD Proposition 3.8, deterministic part: for `u` harmonic on `U₀` and a partition of `3□` into triadic cells of comparable neighbouring sizes, if the triadic cubes `□'` above the cells carry sets `U' ⊆ U₀ ∩ 3□'` with the Sobolev inequality and a moment bound, and `Σ_{x ∈ □} size(x)^t ≤ K\|□\|`, then `E = \|∇u 1_{𝐚≠0}\|²` has `avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. |

The twenty-one theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Partition/`](PercolationClusterHomogenization/Proofs/Partition/) and
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/).

1. **Good cubes and the partition** (`CrossingCluster.lean`, `Adjacent.lean`, `PartitionCube.lean`,
   `AlmostSure.lean`, `GeneralPartition.lean`, `Measurability.lean`, `GoodCubesLocal.lean`). A
   triadic cube of scale at least two is well-connected when it is well-connected relative to its
   rounded three-quarter cube, the notion of the proof of Proposition 2.3; its crossing cluster
   `C_*(Q)` is the union of the open components of `Q` meeting all its faces (AD, Definition 2.5),
   which is then the component of a root. A cube is good when it and its children are well-connected
   (AD, Definition 2.6). Proposition 2.3 bounds the probability that a cube is not good (AD,
   Lemma 2.7), and the stopping-time construction of AD gives the partition `𝒫` into maximal good
   cubes, with its exponential moments, its approximate locality and the measurability of its
   cubes and anchors (AD, Proposition 2.1, for `𝒫` and for a general collection of good cubes).
2. **Paths** (`Adjacent.lean`, `Paths.lean`, `Resolved.lean`, `Local.lean`, `SetCluster.lean`). Two
   good cubes of comparable scales containing lattice neighbours have joined crossing clusters
   (AD, Lemma 2.8), which joins the anchors of the partition cubes along every lattice walk (AD,
   Corollary 2.10). On a cube `U` resolved by the partition (every partition cube meeting `U` lies in
   `U`), every vertex of `C_*(U)` is joined to the anchor of its partition cube by an open path inside
   `C_*(U)` and the `⌈s/10⌉`-neighbourhood of that cube of side `s`.
3. **Minimal scales** (`MinimalScale*.lean`, `Lambda*.lean`, `BadCubes.lean`, `PartitionSize.lean`,
   `StochasticAverage.lean`, `Resolution.lean`). Counting the bad cubes at every scale bounds the sums
   `Σ_{x ∈ □_m} size(□_𝒫(x))^τ` and `Λ_t(□_m)` above a random scale with a stretched exponential
   moment (AD, Proposition 2.4), and bounds the probability that a cube is not resolved.
4. **Coarsening** (`Rigidity/Proofs/Cluster/`: `CoarseData.lean`, `CoarseInequalities.lean`,
   `CoarseNear.lean`, `CoarseReach.lean`, `PartitionCoarseData.lean`, `PartitionReach*.lean`). The
   coarsened function `[w]_𝒫(x) = w(z̄(□_𝒫(x)))` (AD, Definition 3.1) is compared with `w` along the
   paths of step 2 and its gradient along the paths of Lemma 2.8, which gives Lemmas 3.2 and 3.3 of
   AD with the weights described below; every moment of the reach of the partition is finite.
5. **Sobolev inequality** (`CoarseSobolev.lean`, `PartitionSobolev.lean`, `PlanarLatticeSobolev.lean`,
   `PartitionSobolevTwo.lean`, `Sobolev*.lean`). The Sobolev inequality of `ℤᵈ` with zero boundary
   values follows from the `ℓ¹` Sobolev inequality `LatticeHC.sum_rpow_le_sum_abs_grad` (see
   [Copied code](README.md#copied-code)) applied to powers of `\|f\|` and Hölder's inequality; on a cube, a
   function of mean zero is reflected into the triple cube, cut off, and its mean is controlled by
   the `Lᵖ` Poincaré inequality of the cube. Lemmas 3.2 and 3.3 and these inequalities applied to
   `[w]_𝒫` give AD, Proposition 3.4; in the plane the lattice inequality from `ℓ¹` to `ℓ²` is also
   proved directly by comparing the values along rows and columns.
6. **Caccioppoli, reverse Hölder, Gehring and Meyers** (`Caccioppoli.lean`, `ReverseHolder*.lean`,
   `Gehring*.lean`, `Meyers*.lean`). The Caccioppoli inequality on a cluster (AD, Lemma 3.5) uses the
   local Caccioppoli inequality `caccioppoli_of_support` of Lattice-Probability; with the Sobolev
   inequality it gives the reverse Hölder inequality (AD, Lemma 3.6). Gehring's lemma on triadic
   cubes, from a Vitali covering, level sets and the layer-cake formula, applied to the energy
   averaged over the cells of a partition, gives the Meyers estimate (AD, Proposition 3.8).

Departures from Armstrong and Dario:

- **Good cubes.** Cubes of side three are not well-connected in the Lean definition, so good cubes
  have scale at least three: the test cubes of a cube of side three are single points, and the
  uniqueness of the crossing cluster and Lemma 2.8 need not hold for it. The anchor is the point of
  `C_*(Q)` closest to the centre of `Q` in the `ℓ∞` norm, with ties broken lexicographically (AD,
  Definition 3.1); AD, §2, use the Manhattan distance inside the middle child.
- **Paths and the weights of Lemma 3.2.** The proof of AD, Lemma 3.2, joins a vertex to its anchor
  inside the partition cubes at distance at most one from its own, from the identity
  `C_*(□_{n+1}(z)) ∩ □_n(z) = C_∞ ∩ □_n(z)` stated after AD, Definition 2.9, which need not hold at
  the vertices near the boundary of `□_n(z)`. The Lean proof uses the paths of step 2, inside the
  `⌈s/10⌉`-neighbourhood of the partition cube; this neighbourhood can meet much smaller partition
  cubes, so the weight `size(□_𝒫(z))^{sd}` of Lemma 3.2 becomes `3^{sdρ(z)}`, where the reach scale
  `ρ(z) ≥ scale(□_𝒫(z))` is the largest scale of a partition cube whose connecting paths may pass through `z`.
  Lemma 3.3 keeps the weights of AD. Lemmas 3.2 and 3.3 and Proposition 3.4 are proved on cubes
  resolved by the partition, with the weight `3^{tdρ(z)}` in Proposition 3.4.
- **Proposition 3.4.** Three of the four cases of AD are proved: `Σ_{C_*(U)} w = 0`,
  `Σ_U [w]_𝒫 = 0`, and `[w]_𝒫 = 0` on the lattice boundary of `U`, where AD ask for it on the
  boundary `∂_𝐚U` of the cluster, which is smaller; the lattice Sobolev inequality applied to `[w]_𝒫`
  uses the lattice boundary. The case `w = 0` on `∂_𝐚U` is not proved: AD apply Lemmas 3.2 and 3.3
  to the function equal to `[w]_𝒫` off the partition cubes at the boundary and to `0` on them, which
  needs an open path from each point of such a cube, inside cubes of comparable size, to a point of
  `∂_𝐚U`, and AD do not give one.
- **The Sobolev inequality of `ℤᵈ`** is proved, where AD obtain it from that of `ℝᵈ` by affine
  interpolation: with zero boundary values from the `ℓ¹` inequality, and on cubes by reflection and
  the `Lᵖ` Poincaré inequality. It discharges the Sobolev hypothesis `ClusterSobolevTwo` of the
  reverse Hölder inequality in every dimension (`exists_clusterSobolevTwo`); the reverse Hölder and
  Meyers theorems of the table keep the Sobolev inequality as a hypothesis in their statements. The Sobolev inequality on the clusters of integer cubes, and the
  reverse Hölder and Meyers theorems that use it with this hypothesis proved, are in
  [Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55).
- **Proposition 2.4** is proved by counting bad cubes, with a stretched exponential moment of some
  order `r > 0` for the minimal scale in place of every `r < sd/(d + t + s)`. The bound
  `Λ_t(U, 𝒮) ≤ O_{s/t}(C)` stated after the proof of AD, Proposition 2.1, is proved in the form
  `O_{s/(t+d)}(C)`, uniformly in `U` (`LambdaOs.lean`); the order `s/t` cannot hold uniformly when
  `U` is a single vertex, and AD do not use it.
- **Caccioppoli inequality.** Unit conductances, the `ℓ∞` distance of AD, and the constant `8d`;
  for conductances in `[λ, 1]` the constant is `8d/λ` (`caccioppoli_of_distance`).
- **Gehring's lemma.** AD obtain the discrete Gehring lemma from the continuum one by affine
  interpolation; the Lean proof proves it on triadic cubes of `ℤᵈ` directly. The reverse Hölder
  inequality of Step 1 of the proof of AD, Proposition 3.8, is used on the cubes inside `□_{m+1}`
  only, which is all the local Gehring lemma needs, with the energy on `C_*(□_{m+1}) ∩ □`. The
  moment exponent of the Meyers estimate is `t = (2 + ε)(1 + ε)(d + 1)/ε`, twice that of AD.
- **Deterministic parts.** Lemma 3.6 and Proposition 3.8 are proved for every configuration, with
  the Sobolev inequality, the moment bounds and, for the Meyers estimate, the clusters of the
  triadic cubes as hypotheses; the probability bounds of Lemma 3.6 and Proposition 3.8 and the
  partition `ℛ` of AD, Definition 3.7, are not proved in this section; they are proved in
  [Section 3 and the isotropy of the homogenized matrix in every dimension](#section-3-and-the-isotropy-of-the-homogenized-matrix-in-every-dimension).

## Localization of the subadditive quantities and the homogenized matrix for d = 2

Continuing the planar steps of
[Green columns and the coarse-grained cluster for d = 2](https://github.com/nitromannitol/Percolation-Rigidity#green-columns-and-the-coarse-grained-cluster-for-d--2),
the localization and approximate stationarity of `μ` and `ν` (AD, §4.3) and the first step of AD,
§5, the limits of their expectations and the homogenized matrix `ā`, are proved for `d = 2` and
`𝔭_c(2) < p < 1`. Here `ν(□_m, ξ)` and `μ(□_m, q)` are the planar subadditive quantities on the
cluster of the triadic square `□_m` of scale `m` centred at the origin, and the expectations are
taken on the event that the partition exists and resolves `□_m`.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_measure_planarCappedDiscrepancy_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuStationarity.lean) | AD Proposition 4.9 for `d = 2`: the planar partition differs somewhere in a triadic square `V` of scale `n` from the partition capped at scale `n` with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarNuLoc_localization`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuLocal.lean) | AD Proposition 4.10 for `ν`, `d = 2`: a version of `ν(V, ξ)` measurable with respect to the edges near `V` differs from it on an event of probability at most `C exp(−c 3ⁿ)`, and the expectations differ by at most `C\|ξ\|₁² exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarMuLoc_localization`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuLocal.lean) | AD Proposition 4.10 for `μ`, `d = 2`, with the error `C\|q\|₁² exp(−c 3ⁿ)` in expectation. |
| [`Rigidity.Percolation.map_planarNuStat_shift`](PercolationClusterHomogenization/Proofs/Percolation/PlanarLocalStationary.lean) | AD (4.40) for `d = 2`: the law of the local version of `ν(z + □_n, ξ)` does not depend on `z ∈ 3ⁿℤ²`. |
| [`Rigidity.Percolation.map_planarMuStat_shift`](PercolationClusterHomogenization/Proofs/Percolation/PlanarLocalStationary.lean) | the same for `μ`. |
| [`Rigidity.Percolation.exists_tendsto_planarNuMean`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuConvergence.lean) | `E[ν(□_m, ξ)]` converges as `m → ∞`, to a limit between `c\|ξ\|²` and `(9/4)\|ξ\|₁²`. |
| [`Rigidity.Percolation.exists_tendsto_planarMuMean`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuConvergence.lean) | `E[−μ(□_m, q)]` converges as `m → ∞`, to a limit between `0` and `C\|q\|₁²`. |
| [`Rigidity.Percolation.planarNuLimit_eq_planarAhom`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuQuadratic.lean) | AD Definition 5.1 for `d = 2`: the limit is the quadratic form `(1/2) ξ · ā ξ` of a matrix `ā`. |
| [`Rigidity.Percolation.exists_planarAhom_bounds`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuQuadratic.lean) | AD (5.1) for `d = 2`: `c\|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (9/4)\|ξ\|₁²` with `c > 0`. |
| [`Rigidity.Percolation.exists_planarMuLimit_two_sided`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuLimitBounds.lean) | `\|q\|²/18 ≤ lim_m E[−μ(□_m, q)] ≤ C\|q\|₁²`. |
| [`Rigidity.Percolation.sum_mul_le_planarMuLimit_add_planarNuLimit`](PercolationClusterHomogenization/Proofs/Percolation/PlanarDuality.lean) | for all slopes `q` and `ξ`, `q · ξ ≤ lim E[−μ(□_m, q)] + lim E[ν(□_m, ξ)]`. |

The eleven theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Percolation/`](PercolationClusterHomogenization/Proofs/Percolation/), from `PlanarLocality.lean`
and `TriadicCappedPartition.lean` to `PlanarDuality.lean`.

1. **Capped partition and translations** (`TriadicCappedPartition.lean`, `PlanarTranslation.lean`,
   `PlanarAnchorTranslation.lean`, `PlanarClusterTransport.lean`, `PlanarMuTransport.lean`). Declaring
   every cube of scale above `n` good caps the partition at scale `n`; the capped partition and the
   anchors move with the translations of `3ⁿℤ²`, and `μ` and `ν` are invariant under the relabellings
   of the cluster that respect the open edges.
2. **Localization** (`PlanarNuStationarity.lean`, `PlanarNuMeasurable.lean`, `PlanarMuMeasurable.lean`,
   `PlanarLocality.lean`, `PlanarNuLocal.lean`, `PlanarMuLocal.lean`). The partition and its capped
   version differ in `V` with probability at most `C exp(−c 3ⁿ)` (AD, Proposition 4.9). The local
   versions of `ν` and `μ` take the value of `ν` and `μ` at any configuration with the same capped
   cubes, anchors and open edges in the square of side `14 · 3ⁿ` around `V`; they are measurable with
   respect to these edges, hence independent for distant squares (AD, Proposition 4.10).
3. **Stationarity and limits** (`PlanarLocalStationary.lean`, `PlanarLocalLimits.lean`,
   `PlanarNuConvergence.lean`, `PlanarMuConvergence.lean`, `PlanarLimitCubes.lean`). The subadditivity
   of `ν` and `μ` over the resolved subsquares and the approximate stationarity of their expectations
   make `E[ν(□_m, ξ)]` and `E[−μ(□_m, q)]` approximately monotone, with errors
   `C\|ξ\|₁²(3^{−n/2} + exp(−c 3ⁿ))`, so they converge, along every sequence of squares of scale `m`.
4. **The homogenized matrix** (`PlanarNuQuadratic.lean`, `PlanarMuQuadratic.lean`,
   `PlanarMuLimitBounds.lean`, `PlanarDuality.lean`). `ν` and `μ` are quadratic in the slope, so the
   limits are quadratic forms; the limit of `E[ν]` defines `ā` (AD, Definition 5.1), with the bounds
   (5.1), and `q · ξ ≤ ν(U, ξ) − μ(U, q)` passes to the limits.

Departures from Armstrong and Dario:

- **Anchors.** The anchor of a planar partition square is chosen through its displacement from the
  centre of the square, so that anchors move with translations.
- **Localization.** AD define local quantities through the local partitions `𝒫_loc` of
  Proposition 2.1 and use their exact stationarity (4.40); the Lean proof caps the partition at the
  scale of `V`, proves the approximate stationarity of `E[ν]` and `E[−μ]` on resolved squares with
  error `C\|q\|₁² exp(−c 3ⁿ)`, and defines the local versions through the capped partition on the
  square of side `14 · 3ⁿ` around `V`; the stationary versions are taken through the origin square,
  where their laws are exactly invariant.
- **Section 5.** This section proves the convergence of the expectations, Definition 5.1 and (5.1),
  and the inequality `q · ξ ≤ lim E[−μ] + lim E[ν]`; the identification
  `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` and the further parts of AD, §5, are in
  [Energy defects, finite-volume matrices and the identification of the limit for d = 2](#energy-defects-finite-volume-matrices-and-the-identification-of-the-limit-for-d--2).

## Energy defects, finite-volume matrices and the identification of the limit for d = 2

Continuing [the previous section](#localization-of-the-subadditive-quantities-and-the-homogenized-matrix-for-d--2),
the parts of AD, §5, that do not use the Meyers estimate on the cluster are proved for `d = 2` and
`𝔭_c(2) < p < 1`. Write `ε_k = 3^{−k/2} + exp(−c 3ᵏ)`. The quantity `τ_k` of AD, §5, is the sum of
the positive parts of the increments of `E[μ(□_k, ·)]` at the unit vectors and of `E[ν(□_k, ·)]` at
`ā⁻¹` applied to them. The matrix `ā_{□_n}⁻¹` of AD, Definition 5.6, is the matrix of the quadratic
form `2 E[−μ(□_n, ·)]`. The expectation of `ω(□_n, q)` is
`E[ν(□_n, ā⁻¹q)] + E[−μ(□_n, q)] − q · ā⁻¹q`, and `D_n` is the quantity of the proof of AD,
Lemma 5.10. The numbering is that of the arXiv v2 source: Definition 5.6 precedes the weak
convergence Lemma 5.7, the flatness Lemma 5.8, the decay of `ω` Lemma 5.9 and its iteration
Lemma 5.10.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.sum_clusterForm_sub_add_sum_planarMu_subcubes_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarSecondVariation.lean) | AD Lemma 4.2 and (5.11) for `μ`, `d = 2`: for the minimizer on a resolved cube and the minimizers on its subcubes of scale `n`, the energy of the differences plus the sum of `μ` over the subcubes is at most `μ` of the large cube. |
| [`Rigidity.Percolation.sum_clusterForm_sub_add_planarNu_le_sum_subcubes`](PercolationClusterHomogenization/Proofs/Percolation/PlanarSecondVariation.lean) | the same for `ν`, for any solution of the first variation equation on the large cube. |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuEnergyDefect.lean) | AD Lemma 5.4, display (5.10), for `μ`: the expected energy of the differences between the restricted minimizer and the minimizers on the subcubes of scale `n` is at most the volume times the decrease of `E[−μ]` between the two scales, up to `C\|q\|₁² ε_n`. |
| [`Rigidity.Percolation.exists_lintegral_planarNuDefect_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuEnergyDefect.lean) | the same for `ν`, with maximizers. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_planarMuTau`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuIncrements.lean) | AD (5.9) and (5.10) for `μ`: for `n ≤ m`, the expected energy of the differences, divided by the volume, is at most `2\|q\|² ∑_{n ≤ k < m} τ_k^μ` plus `C\|q\|₁² (∑_{n ≤ k < m} ε_k + ε_n)`. |
| [`Rigidity.Percolation.exists_planarNuDefect_le_planarNuTau`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTau.lean) | the same for `ν` at `ā⁻¹ q`, with `τ^ν`. |
| [`Rigidity.Percolation.summable_planarTau`](PercolationClusterHomogenization/Proofs/Percolation/PlanarTauSummable.lean) | `τ_k` is summable. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_tendsto`](PercolationClusterHomogenization/Proofs/Percolation/PlanarTauSummable.lean), [`exists_planarNuDefect_le_tendsto`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTau.lean) | AD Lemma 5.4, qualitative form: the expected energy of the differences divided by the volume is at most `(\|q\|² + \|q\|₁²) R_n` with `R_n → 0`, uniformly in `m ≥ n`. |
| [`Rigidity.Percolation.planarMuLimit_eq_iff_planarOmegaLimit_eq_zero`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaLimit.lean), [`forall_planarOmegaLimit_eq_zero_iff`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMatrix.lean) | AD Proposition 5.2: the limit of `E[ω(□_n, q)]` exists and is nonnegative, and `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for all `q` if and only if the limit of `E[ω]` vanishes, if and only if the finite-volume matrices converge to `ā⁻¹`. |
| [`Rigidity.Percolation.integral_coarsePairing_planarMuMinimizer`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | AD (5.23), the centering in Lemma 5.7: the expected spatial average of the coarsened gradient of the minimizer of `μ(□_n, q)` against `r` is `r · ā_{□_n}⁻¹ q`. |
| [`Rigidity.Percolation.tendsto_planarAhomInvFinite`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | the matrices `ā_{□_n}⁻¹` converge entrywise to twice the matrix of the limit of `E[−μ]`. |
| [`Rigidity.Percolation.exists_planarAhomInvFinite_bounds`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeBounds.lean), [`exists_abs_planarAhomInvFinite_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeClose.lean) | AD (5.22) and (5.24): the matrices are uniformly elliptic from some scale on, and two of them differ by at most `2 ∑ τ_k` plus a vanishing error. |
| [`Rigidity.Percolation.tsum_sum_grad_mul_solenoidalField`](PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalPairing.lean), [`solenoidalField_eq`](PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalField.lean), [`abs_solenoidalField_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalField.lean) | AD Lemma 5.7, Step 1, and (5.28) with right side zero, `d = 2`: a finitely supported, exactly divergence free field, bounded by `10 \|e\|₁`, equal to `e` near `□_n`, is orthogonal to every gradient. |
| [`Rigidity.Percolation.exists_abs_planarNu_sub_planarMu_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarQuadraticResponse.lean) | first display of the proof of AD Lemma 5.9, per cube: `ν(U, p) − μ(U, q) − q · p` differs from the energy of the difference between the maximizer and the minimizer, divided by twice the volume, by at most `\|q · p\|/L` plus the boundary error. |
| [`Rigidity.Percolation.exists_planarOmegaD_succ_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaStepOne.lean), [`exists_neg_le_planarOmegaD`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDBounds.lean) | AD Lemma 5.10, Step 1 and the lower bound of `D_n`: from some scale on, `D_{n+1} ≤ D_n − c τ_n + C ε_n` and `D_n ≥ −C 3^{−n/2}`. |
| [`Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIteration.lean), [`exists_le_mul_pow_of_omega_iteration_of_ge`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIteration.lean) | AD Lemma 5.10, Steps 1 to 3, for real sequences, also when the hypotheses hold only from a starting scale on. |
| [`Rigidity.Percolation.exists_planarOmegaD_le_pow_of_decay`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_planarTau_le_pow_of_decay`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_abs_planarAhomInvLimit_sub_le_of_decay`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeRate.lean) | AD Lemma 5.10 with the bound of Lemma 5.9 as an explicit hypothesis `h59`: `D_n`, `τ_n` and the distance from `ā_{□_n}⁻¹` to its limit decay geometrically. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_decay`](PercolationClusterHomogenization/Proofs/Percolation/PlanarIdentification.lean) | AD Proposition 5.2, qualitative part, with the bound of Lemma 5.9, `D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n−l} τ_l)` from some scale on with `σ, ρ < 1`, as an explicit hypothesis: `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. |

The theorems of the table and their supporting results (the limit matrix is invertible, the matrices
`ā_{□_n}` converge to its inverse, `D_n` converges, the limit matrix is below `ā⁻¹`) depend on
exactly `propext`, `Classical.choice` and `Quot.sound`; thirty-five of them have axiom reports in
[`Audit/Axioms.lean`](Audit/Axioms.lean). The modules are in
[`PercolationClusterHomogenization/Proofs/Percolation/`](PercolationClusterHomogenization/Proofs/Percolation/), from `PlanarSecondVariation.lean`
and `PlanarMuEnergyDefect.lean` to `PlanarIdentification.lean`.

1. **Energy defects** (`PlanarSecondVariation.lean`, `PlanarMuEnergyDefect.lean`,
   `PlanarNuEnergyDefect.lean`). The second variation identities for `μ` and `ν` on a resolved
   cube and their subadditive form, summed over the subcubes of scale `n`, bound the energy of the
   differences between the restricted optimizer and the optimizers of the subcubes by the decrease
   of the expectation between the two scales.
2. **The quantity `τ`** (`PlanarMuIncrements.lean`, `PlanarNuIncrements.lean`,
   `PlanarNuDefectTau.lean`, `PlanarTauSummable.lean`). The increments of the expectations are
   almost nonnegative quadratic forms, controlled by their values at the unit vectors, so that the
   energy defects are controlled by the sums of `τ_k`, which are summable.
3. **Finite-volume matrices** (`PlanarFiniteVolumeMatrix.lean`, `PlanarFiniteVolumeInverse.lean`,
   `PlanarFiniteVolumeBounds.lean`, `PlanarFiniteVolumeClose.lean`,
   `PlanarFiniteVolumeInverseLimit.lean`, `PlanarCoarseGradientMean.lean`). The matrices
   `ā_{□_n}⁻¹` and their inverses, their ellipticity, their closeness at two scales and their
   limit.
4. **Solenoidal field** (`PlanarSolenoidalField.lean`, `PlanarSolenoidalPairing.lean`). The
   discrete curl of a cut off affine stream function on the plaquettes.
5. **The quantity `ω` and the identification** (`PlanarOmegaLimit.lean`, `PlanarOmegaMatrix.lean`,
   `PlanarOmegaDLimit.lean`, `PlanarQuadraticTrace.lean`, `PlanarOmegaStepOne.lean`,
   `PlanarOmegaDBounds.lean`, `PlanarOmegaIteration.lean`, `PlanarOmegaDecayIteration.lean`,
   `PlanarFiniteVolumeRate.lean`, `PlanarIdentification.lean`, `PlanarQuadraticResponse.lean`). The
   limit of `E[ω]` and its vanishing, the decrease of `D_n` along `τ_n`, the iteration of AD,
   Lemma 5.10, and the identification of the limit of `E[−μ]` from the bound of Lemma 5.9.

Departures from Armstrong and Dario:

- **Hypothesis of the identification.** In this section the bound of Lemma 5.9 for `D_n` is not proved
  (it is proved from Lemmas 5.5 and 5.7 in
  [Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2](#lemmas-58-and-59-and-the-qualitative-part-of-proposition-52-for-d--2)). Its proof
  uses Lemmas 5.5 to 5.8, and Lemma 5.5, with Steps 2 and 3 of Lemma 5.7, needs the Meyers estimate
  of AD, Proposition 3.8, on the planar cluster, which is proved in a deterministic form with its
  good events as hypotheses in
  [Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55).
  The theorem `planarMuLimit_eq_of_decay` and the geometric rates derived from Lemma 5.10 therefore
  take the bound as the explicit hypothesis `h59`; without it, the identification is reduced to the
  vanishing of the limit of `E[ω]`. The rate of Proposition 5.2 in expectation, Lemma 5.10, Lemma 5.11 Step 2 and a deterministic form of
  Lemma 5.3 are proved for `p > 𝔭_c(2)` in [The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two](#the-rate-of-proposition-52-and-lemmas-53-510-and-511-step-2-in-dimension-two); Proposition 5.2 in the `O_s` form, Lemma 5.11 and
  Proposition 5.13 are proved in [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two). Lemmas 5.5 and 5.7 in `d = 2` are proved in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).
- **Lemma 5.4.** The estimate is proved for every `n ≤ m` with the error
  `C\|q\|₁² (∑_k ε_k + ε_n)`, `ε_k = 3^{−k/2} + exp(−c 3ᵏ)`, where AD take `n ∈ [m/2, m)` and the
  error `3^{−n/4}`; the quantity `τ^ν` is built at `ā⁻¹ e_i`, as in AD.
- **Lemma 5.7.** The field of Step 1 is the discrete curl of a cut off affine stream function, so
  it is exactly divergence free and supported in the square of half side `5/4 · 3ⁿ + 1`, whereas AD
  discretize a smooth field that is almost divergence free. Steps 2 and 3 are not proved in this
  section; see [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).
- **Lemma 5.10, Step 2.** The display for `D̃_n − D̃_{n+1}` has `D_k − D_{k−1}` where `D_k − D_{k+1}`
  is meant, and the bound of Lemma 5.9 is resummed over `l ∈ [N₀, n]` where `l ≤ k` is meant, the
  terms with `l < N₀` being `O(3^{N₀−k})`. The Lean proof uses the exact recursions
  `D̃_{n+1} = μ D̃_n + D_{n+1}` for the weighted averages instead.

## Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5

Armstrong and Dario use the reverse Hölder inequality of Lemma 3.6 on every triadic cube `□'`
above a cell of the Gehring partition, with the Sobolev inequality of Proposition 3.4 on the cluster
of the triple `3□'`, which is an integer cube of side `3^{k+1}` but in general not a triadic cube.
Here Lemmas 3.2 and 3.3 and Proposition 3.4 (with `s = 2` and `∑_{C(B)} w = 0`) are proved on the
cluster `C(B)` of every integer cube `B` resolved by the partition, in every dimension `d ≥ 2`, and
the deterministic part of the Meyers estimate (AD, Proposition 3.8) and of Step 3 of the proof of
Lemma 5.5 follow in `d = 2`. The results are conditional: each states, as hypotheses, exactly the
events and moment bounds listed in its row, which are not proved here.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube_of_moment`](PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderMoment.lean), [`reverse_holder_partition_of_moment`](PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderMoment.lean) | AD Lemma 3.6, deterministic part, every `d ≥ 2`, with the Sobolev hypothesis proved: for a resolved cube `□_{m+1}` with `∑_{z ∈ C_*(□_{m+1})} (3^{ρ(z)})^{2ds} ≤ C_G \|□_{m+1}\|` and `u` harmonic on `C_*(□_{m+1})`, `3^{−md} ∑_{C_*(□_{m+1}) ∩ □_m} \|∇u 1_{𝐚≠0}\|² ≤ C (\|□_{m+1}\|⁻¹ ∑_{C_*(□_{m+1})} \|∇u 1_{𝐚≠0}\|^{t 2_*})^{2/(t 2_*)}`, as in `reverse_holder_partition_cube`. |
| [`Rigidity.Proofs.Cluster.planar_reverse_holder_cube_of_moment`](PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderPlanar.lean) | the same for the planar partition, with the weight `((3^ρ)² + 3^{ρ'})^{1/4}` and the moment bound `∑ ((3^ρ)² + 3^{ρ'})^s ≤ C_G 3^{2(m+1)}`. |
| [`Rigidity.Percolation.exists_planarBox_sum_sq_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarBoxSobolev.lean), [`exists_clusterSobolevTwo_box`](PercolationClusterHomogenization/Proofs/Cluster/PartitionBoxSobolev.lean) | AD Proposition 3.4 with `s = 2`, with Lemmas 3.2 and 3.3 proved on the cluster of an integer square (`d = 2`) or integer cube (every `d ≥ 2`) `B` resolved by the partition, for `w` of mean zero on the cluster: `∑_{C(B)} w² ≤ K (∑_{z ∈ C(B)} w_ρ(z) \|∇w 1_{𝐚≠0}\|(z))²` with the weight `w_ρ` built from the reach scales of `B`, which are bounded by the reach of the partition (`three_pow_reachScale_le_planarReach_box`, `three_pow_reachScale_le_partitionReach_box`). |
| [`Rigidity.Proofs.Cluster.reverse_holder_clusterEnergy_local`](PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean), [`meyers_cluster_of_local`](PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean) | the reverse Hölder inequality for functions harmonic near the cube, and `meyers_cluster` with a weight chosen for each cube `□'`. |
| [`Rigidity.Proofs.Cluster.planar_meyers`](PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean), [`planar_meyers_clusterHarmonic`](PercolationClusterHomogenization/Proofs/Cluster/PlanarMeyersHarmonic.lean) | AD Proposition 3.8, deterministic part, `d = 2`, with the Sobolev inequality on the clusters of the triples proved, for `u` harmonic on the cluster of a triadic cube `V ⊇ 3□` (for the extension by zero of a harmonic function of a smaller cube in the second form). Hypotheses: the planar partition event; a Gehring partition of `3□` into cells of comparable neighbouring sizes with `∑_{x ∈ □} (3^{s(x)})^t ≤ K \|□\|`; for every triadic `□' = cube k y` above a cell with `3□' ⊆ 3□`, the partition cubes of the vertices of `3□'` have scale at most `k` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G \|3□'\|`. |
| [`Rigidity.Proofs.Cluster.partition_meyers`](PercolationClusterHomogenization/Proofs/Cluster/MeyersPartitionBox.lean) | the same in every dimension `d ≥ 2` on `C_*(V) ∩ 3□`, `V` resolved, with `∑_{z ∈ 3□'} partitionReach(z)^{2d(d+2)} ≤ C_G \|3□'\|` and the partition scales below `k`. |
| [`Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMeyers.lean), [`planarBox_coarse_energy_le_of_meyers`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMeyers.lean) | AD display (5.16), deterministic, `d = 2`: with the Meyers estimate on cells `□'` covering the cluster of a resolved square `B ⊆ V`, triples of overlap at most `N`, and cell averages of a weight `W ≥ 3^{ρ'}` with `(avg_{□'} W^{3q})^{1/q} ≤ A`, `∑_B \|∇[w]_𝒫\|² ≤ C² A C_M^{1/p} N ∑_V \|∇w 1_{𝐚≠0}\|²`. |
| [`Rigidity.Percolation.edgePairing_sq_le_of_subset`](PercolationClusterHomogenization/Proofs/Cluster/PlanarEdgePairing.lean), [`coarsePairing_eq_edgePairing`](PercolationClusterHomogenization/Proofs/Cluster/PlanarEdgePairing.lean) | AD Lemma 5.5, Step 2 (removal of the boundary layer): `⟨∇f, g⟩_V² ≤ 8 G² \|B\| E_B + 16 G² \|V ∖ B\| E_V` for `\|g\| ≤ G`. |
| [`Rigidity.Proofs.Cluster.edgePairing_clusterExtend_sq_le_clusterForm`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergy.lean), [`edgePairing_innerCells_sq_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarInnerCells.lean) | AD Lemma 5.5, Steps 2 and 3 on one subcube, with the Hölder inequality inside the cells of scale `j` of the inner square: `⟨∇[w]_𝒫, g⟩_V² ≤ Λ B(w, w)`. Hypotheses: the partition scales on `V` are at most `j`, the Meyers estimate for `w` on the cells, the bound `A` on the cell averages of the weight, and `W ≥ 3 planarReach` on the cluster. |
| [`Rigidity.Proofs.Cluster.sum_edgePairing_sq_le_planarMuDefect`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictDefect.lean) | AD Lemma 5.5, deterministic part, summed over the resolved subcubes of scale `n`: `∑_V ⟨∇[w_V]_𝒫, g⟩_V² ≤ 2 Λ D_n(U, q)`, with the hypotheses of `edgePairing_innerCells_sq_le` on each subcube. |
| [`Rigidity.Percolation.exists_measure_partitionScale_gt_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarPartitionScaleTail.lean) | for every `m`, the probability that some vertex of a finite set `S` has a planar partition cube of scale larger than `j` is at most `C \|S\| 3^{−(j+1)(m+1)}`. |
| [`Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMinimizer.lean), [`exists_lintegral_coarse_minimizer_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergyMoments.lean), [`exists_lintegral_coarse_minimizer_sq_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergySecondMoment.lean) | AD (4.24), `d = 2`: for the minimizer `u_V` of `μ(V, q)` on a resolved triadic cube, `∑_V \|∇[u_V]_𝒫\|² ≤ C \|q\|₁² (3 max_V R)³ ∑_V R⁴` with `R = planarReach`, `E[∑_V \|∇[u_V]_𝒫\|²] ≤ C_a \|q\|₁² \|V\|^{1+1/a}` for `a ≥ 2`, and the second moment `≤ C \|q\|₁⁴ \|V\|^{2+2/a}` for `a ≥ 3`. |
| [`Rigidity.Percolation.edgePairing_sub_sum_subcubes_sq_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSubcubePairing.lean), [`Rigidity.Proofs.Cluster.exists_lintegral_edgePairing_sub_sum_subcubes_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarHolderAway.lean) | AD Lemma 5.7, Step 2, display (5.29), `d = 2`: the pairing of a bounded field with the coarsened gradient on `U` differs from the sum over the subcubes of scale `n` by at most the number of crossing edges times the energy, and in expectation `E[(⟨∇[u_U], g⟩_U − ∑_V ⟨∇[u_U], g⟩_V)²] ≤ C G² \|q\|₁² 3^{−n} \|U\|² \|U\|^{1/a}`. |

The theorems of the table and their supporting results depend only on axioms among `propext`, `Classical.choice`
and `Quot.sound`; sixty-five of them (sixty-one theorems and four definitions) have axiom reports in
[`Audit/Axioms.lean`](Audit/Axioms.lean). The modules are in
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/), from `ReverseHolderMoment.lean` to
`PlanarRestrictDefect.lean`.

1. **Windows and clusters of integer cubes** (`PlanarBoxWindows.lean`, `PlanarBoxCluster.lean`,
   `PartitionBoxPaths.lean`, `PartitionBoxCluster.lean`). A vertex joined to the anchor of its
   partition cube by a path that leaves the integer cube only far from the vertex is joined to it
   inside the window of the cube; the cluster `C(B)` of an integer cube resolved by the partition is
   the set of vertices of `B` joined inside `B` to the anchor of their partition cube, and its
   coarse-graining data are built from the windows and pair windows inside `B`.
2. **Sobolev inequality and Meyers estimate** (`PlanarBoxSobolev.lean`, `PartitionBoxSobolev.lean`,
   `ReverseHolder*.lean`, `Meyers*.lean`, `PlanarMeyersHarmonic.lean`). Lemmas 3.2 and 3.3 and the
   lattice Sobolev inequality on integer cubes give Proposition 3.4 on `C(B)`, and with it the
   reverse Hölder inequality at every cube used by the Gehring argument.
3. **Coarse energy of Lemma 5.5** (`PlanarCoarseMeyers.lean`, `PlanarEdgePairing.lean`,
   `PlanarInnerSquare.lean`, `PlanarInnerCells.lean`, `PlanarRestrictQuad.lean`,
   `PlanarRestrictCoarse.lean`, `PlanarCoarseEnergy.lean`, `PlanarRestrictDefect.lean`). The Meyers
   estimate on the cells of the inner square, Lemma 3.3 and the Hölder inequality bound the energy
   of the coarsened differences of the minimizers, and the pairing with a bounded field, by the
   energy defect of Lemma 5.4.
4. **Moments** (`PlanarCoarseMinimizer.lean`, `PlanarCoarseEnergyMoments.lean`,
   `PlanarCoarseEnergySecondMoment.lean`, `PlanarPartitionScaleTail.lean`,
   `PlanarSubcubePairing.lean`, `PlanarHolderAway.lean`). The reach of the planar partition has all
   moments, which bounds the coarsened energy of the minimizers in expectation (AD (4.24)) and the
   probability that a partition cube is larger than a given scale.

Departures from Armstrong and Dario:

- **Clusters of the triples.** AD apply Proposition 3.4 on `C_max(3□')`; the Lean proof uses the
  cluster `C(3□')` of the integer cube, the vertices joined to the anchor of their partition cube
  inside it. It lies in the crossing cluster of every resolved triadic cube containing `3□'`, is
  closed under open edges inside `3□'`, and contains the vertices of the crossing cluster in `□'`.
  The weight of the Sobolev inequality is the reach of the partition, not the size of the partition
  cube.
- **Reverse Hölder inequality at non-central cubes.** AD prove Lemma 3.6 for central subcubes of a
  triadic cube and obtain the other cubes of the proof of Proposition 3.8 by stationarity. The Lean
  proof of the Meyers estimate derives the inequality at every `□'` from the Caccioppoli
  inequality and the Sobolev inequality on `C(3□')`, and takes the good event of the partition
  `ℛ` at `□'` as a hypothesis in place of the stationarity.
- **Departure from AD18, Lemma 5.5 Step 3: Hölder inside the cells (AD, arXiv v2 numbering, display after "apply the proposition in each
  `Q'`").** The second inequality of the display,
  `(\|□_n\|⁻¹ ∑ \|Q'\|^{1−s/2} a_{Q'}^{s/2})^{2/s} ≤ \|□_n\|⁻¹ ∑ \|Q'\|^{2/s−1} a_{Q'}`, is not true
  as written: by concavity the right side carries `\|□_n\|^{−2/s}`, and for one charged unit cell
  the two sides differ by the factor `\|□_n\|^{1−2/s}`; the global Hölder inequality over the cells
  loses the power `(#cells)^{(s−2)/s}` (it is `sum_rpow_le_of_meyers_cells`). The repair is the
  Hölder inequality inside each cell with the cell average of the weight (`sum_mul_le_of_meyers_cells`),
  the cells being the triadic squares of scale `⌈n/2⌉` not touching the boundary of the subcube, on
  the event that the Meyers estimate holds on all cubes of scale at least `⌈n/2⌉` and the cell
  averages of the weight are bounded. The weight is the pair reach of the partition, bounded by
  three times the reach of the planar partition, in place of the sizes of the partition cubes.
- **Display (4.24) and the moments.** The bounds are proved with the reach of the planar partition
  and the factor `\|V\|^{1/a}` for every `a ≥ 2` in place of `3^{δ n}`, `δ > 0`; the second moment
  is added for the estimates off the good events.
- **Conditional statements.** The Meyers estimate (`planar_meyers`, `partition_meyers`), the
  per-subcube bound `edgePairing_innerCells_sq_le` and its sum over the subcubes
  `sum_edgePairing_sq_le_planarMuDefect` are deterministic: the good events they assume (the
  Gehring partition and the bounds on the reach over the triples, the partition scales and the
  Meyers estimate on the cells of the inner squares, the bounds on the cell averages of the weight)
  are not shown to hold with high probability in this section. Consequently Lemma 5.5 itself and
  Lemma 5.7 Step 3 are not proved here; they are proved for `p > 𝔭_c(2)` in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two). Lemmas 5.8 and 5.9 are proved from Lemmas 5.5 and 5.7 in
  [Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2](#lemmas-58-and-59-and-the-qualitative-part-of-proposition-52-for-d--2).

## The subadditive quantities on the clusters of triadic cubes of Z^d

Section 4 of Armstrong and Dario defines `μ(U, q)` and `ν(U, p)` on the cluster `C_*(U)` of a
resolved triadic cube `U` of `ℤ^d`, and proves their basic properties. For `d = 2` this is in
[Localization of the subadditive quantities and the homogenized matrix for d = 2](#localization-of-the-subadditive-quantities-and-the-homogenized-matrix-for-d--2)
and the sections after it. Here the same results are proved in every dimension `d ≥ 2`, in
[`PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/), with the names
`cubeMu`, `cubeNu`, `cubeForm`, `cubeHarmonic` in place of the planar `planarMu`, `clusterForm`, and
so on. On the partition event and for a resolved cube, `cl_𝒫(U) = U` and `C_*(U)` is the crossing
cluster of `U`; the space `A_*(U)` of the paper is `cubeHarmonic`, the functions on `C_*(U)` harmonic
at the vertices of `C_*(U)` in the lattice interior of `U`. AD numbering below is that of the arXiv v2
source (Definition 4.1, Lemmas 4.2 to 4.5, Corollary 4.6, Lemmas 4.7 and 4.8, Definition 5.1).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.cubeMu`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`cubeNu`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeMu_minimizer`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeNu_maximizer`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean) | AD Definition 4.1 and Lemma 4.2: `μ(U, q) = inf_{A_*(U)} (B(u, u)/2 − ℓ_q(u))/\|U\|` and `ν(U, p) = sup_{A_*(U)} (F_p(v) − B(v, v)/2)/\|U\|` are attained, at solutions of the first variation equations `B(w, u) = ℓ_q(w)` and `B(w, v) = F_p(w)` for `w ∈ A_*(U)`; here `B` is the Dirichlet form on the open edges of `C_*(U)`, `ℓ_q` the coarse pairing over the lattice edges inside `U`, and `F_p` the flux pairing. |
| [`cubeMu_mul_latticeVolume_add_cubeForm_sub`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeFluxPairing_sub_add_cubeForm_sub`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_mul_latticeVolume_eq`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_mul_latticeVolume_eq`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_sub_cubeMu_eq`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_smul_add_smul`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_smul_add_smul`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean) | AD Lemma 4.2, (4.4), (4.6), (4.7) and (4.8): the second variations, the values `\|U\| μ(U, q) = −B(u, u)/2` and `\|U\| ν(U, p) = B(v, v)/2` at the optimizers, the comparison identity of `ν` and `μ`, and the quadratic dependence of `μ` and `ν` on `q` and `p`. |
| [`cubeMu_nonpos`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_nonneg`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`neg_cubeMu_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuUpperBound.lean), [`exists_lintegral_neg_cubeMu_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuMoment.lean) | `μ(U, q) ≤ 0 ≤ ν(U, p) ≤ (3^d/4) \|p\|₁²` ((4.13)); the bound of `−μ` by the partition sizes, `−μ(U, q) ≤ d C₃² \|q\|₁² \|U\|⁻¹ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d−2}` ((4.12)), through AD Lemma 3.3 with `s = 1`; and `E[−μ(U, q); partition event, U resolved] ≤ C \|q\|₁²` ((4.16), in expectation). |
| [`exists_cubeNu_maximizer_affine`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeHarmonic_eq_on_boundary`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`cubeNu_le_of_affine_boundary`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeNu_eq_of_affine_boundary`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean) | AD Lemma 4.3, (4.1) and (4.9): the functions vanishing outside the lattice interior of `U` are orthogonal to `A_*(U)`, the Dirichlet problem on `C_*(U)` with any boundary values is solvable, the maximizer of `ν(U, p)` is affine of slope `p` at the boundary vertices of `C_*(U)` up to a constant, and `ν(U, p) \|U\|` is the least half energy of a function with such boundary values. |
| [`cubeCoarsePairing_eq_faces`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeStokes.lean), [`abs_cubeCoarsePairing_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNablaAffine.lean), [`cubeBoundaryError_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeBoundaryErrorBound.lean), [`cubeBoundaryWeight_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeBoundaryWeightBound.lean), [`exists_integral_sum_faces_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean), [`exists_integral_sum_margin_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean) | AD Lemma 4.5, (4.27), in every dimension: by the discrete Stokes formula the coarse pairing is a sum of coarsened values over the faces of `U`; for the maximizer `v` of `ν(U, p)`, `\|ℓ_q(v) − (q · p) L^{d−1}(L − 1)\| ≤ \|q\|₁ E_p(v)`, the boundary error `E_p(v)` being a weighted variation of `v` over the partition cubes at the faces, bounded by the Hölder and Young inequalities through the weight `W_∂(z) ≤ ∑_i 2 size(□_𝒫(z))^{d−1} 1{margin_i(z) < size(□_𝒫(z))}`; and the expectations of the sums of the sizes over the faces and of the margin-weighted sums are at most `C L^{d−1}`. |
| [`exists_abs_cubeNu_sub_cubeMu_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean), [`exists_cubeMu_le_cubeNu_sub`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean) | AD Corollary 4.6, (4.29): `\|ν(U, p) − μ(U, q) − q · p − B(v − u, v − u)/(2\|U\|)\| ≤ \|q · p\|/L + \|q\|₁ E_p(v)/\|U\|`, with `E_p(v)` the boundary error, and `μ(U, q) ≤ ν(U, p) − q · p` up to the same errors. |
| [`exists_cubeMu_le_neg_sum_sq`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuLowerBound.lean), [`le_cubeNu_add_of_resolved`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBound.lean), [`exists_le_integral_cubeNu`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Lemma 4.7, (4.30) and (4.31): `μ(U, q) ≤ −\|q\|²/(3^d d) + t \|q\|²/L + \|q\|₁ E_{tq}(v)/\|U\|` with `t = 2/(3^d d)`; `κ \|p\|² ≤ ν(U, p)` up to explicit errors for every `κ > 0`; and, in expectation, `c \|p\|² ≤ E[ν(U, p)] + C \|p\|₁² 3^{−m/2}` for every triadic cube `U` of scale `m`. |
| [`sum_cubeMu_subcubes_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`cubeNu_le_sum_subcubes`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`flux_error_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`cubeNu_mul_latticeVolume_le_sum_add`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`sum_exp_neg_margin_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeExceptionalTail.lean) | AD Lemma 4.8, (4.32) and (4.33): for a resolved `U` and `n ≤` the scale of `U`, the sum over the vertices `x` of `U` of `μ(V(x), q)` over the resolved subcubes `V(x)` of scale `n` is at most `\|U\| μ(U, q)` plus the coarse pairing of the minimizer over the exceptional lattice edges, and `\|U\| ν(U, p)` is at most the sum over `x` of `ν(V(x), p)` plus the flux pairing of the maximizer over the open edges not inside the cluster of a resolved subcube; the second is bounded by `(3^d/4) \|p\|₁² (s G + \|U\|/s)` for every `s > 0`, `G` the number of exceptional vertices. |
| [`sum_cubeForm_sub_add_sum_cubeMu_subcubes_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`sum_cubeForm_sub_add_cubeNu_le_sum_subcubes`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`cubeNuDefect_add_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean), [`exists_lintegral_cubeNuDefect_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean) | the subadditivity of `μ` and `ν` with the energies of the differences on the left side (AD, proof of Lemma 5.4, (5.11) and its analogue for `ν`): `∑_V B_V(u\|_V − u_V)/2 + ∑_V \|V\| μ(V, q) ≤ \|U\| μ(U, q) + E_q(u)` and `∑_V B_V(v\|_V − v_V)/2 + \|U\| ν(U, p) ≤ ∑_V \|V\| ν(V, p) + F_p^{exc}(v)`; and the expectation of the energy `D^ν_n(U, p)` of the differences of the maximizers of `ν` is at most `\|U\| (E[ν(V, p)] − E[ν(U, p)] + C \|p\|₁² 3^{−n/2})`. |
| [`cubeNu_eq_of_equiv`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`measurable_cubeNu`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integral_cubeNu_eq_of_scale_eq`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integrable_cubeNu`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean) | `ν(U, p)` depends only on the open edges inside `U`, is a measurable and integrable function of the configuration, and `E[ν(U, p)]` is the same for all triadic cubes of a given scale (exact stationarity). |
| [`exists_integral_cubeNu_le_of_scale_le`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuMonotone.lean) | AD (4.49), every `d ≥ 2`: `E[ν(U, p)] ≤ E[ν(V, p)] + C \|p\|₁² 3^{−n/2}` for triadic cubes `V`, `U` of scales `n ≤ m`. |
| [`cubeNu_eq_sum_polarization`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_tendsto_cubeNuMean`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`tendsto_cubeNuLimit`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeNuLimit_eq_cubeAhom`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_symm`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_bounds`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_cubeAhom_lower_bound`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Definition 5.1 and (5.1), every `d ≥ 2`: `ν(U, ·)` is a quadratic form given by polarization; `E[ν(□_m, ξ)]` converges as `m → ∞`; the limit is `(1/2) ξ · ā ξ` for a symmetric matrix `ā = cubeAhom`, and `c \|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (3^d/4) \|ξ\|₁²`. |

The theorems of the table and their supporting results depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`; fifty-seven of them (fifty-four theorems and three definitions)
have axiom reports in [`Audit/Axioms.lean`](Audit/Axioms.lean). The modules are the
twenty-four files of [`PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/`](PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/).
The quantities `cubeMu` and `cubeNu` at `d = 2` are not identified with the planar `planarMu` and
`planarNu`: the planar quantities are built on the meshed family of good squares, the general ones
on the partition into good cubes of every dimension.

1. **Cluster and variational structure** (`CubeEnergy.lean`, `CubeVariations.lean`,
   `CubeEnergyBounds.lean`, `CubeNuDirichlet.lean`). The cluster, the Dirichlet form, the two
   pairings and the quantities `μ`, `ν`, with their first and second variations and the Dirichlet
   problem with affine data.
2. **Boundary terms and comparison** (`CubeStokes.lean`, `CubeNablaAffine.lean`,
   `CubeBoundaryErrorBound.lean`, `CubeBoundaryWeightBound.lean`, `CubeSizeMoments.lean`,
   `CubeMuNuComparison.lean`, `CubeMuUpperBound.lean`, `CubeMuLowerBound.lean`,
   `CubeNuLowerBound.lean`, `CubeNuLowerBoundMean.lean`, `CubeMuMoment.lean`). The coarse pairing as
   a sum over the faces, the boundary error of the maximizer of `ν`, the bounds on `μ` and `ν`
   and their expectations.
3. **Subadditivity and the limit** (`CubeSubcubes.lean`, `CubeSubadditive.lean`,
   `CubeSecondVariation.lean`, `CubeNuSubadditiveError.lean`, `CubeExceptionalTail.lean`,
   `CubeNuMonotone.lean`, `CubeNuEnergyDefect.lean`, `CubeNuLocal.lean`, `CubeNuLimit.lean`). The
   restriction of functions to resolved subcubes, the subadditivity inequalities, the exceptional
   vertices, the stationarity and approximate monotonicity of `E[ν]`, and the homogenized matrix.

Departures from Armstrong and Dario:

- **Resolved triadic cubes.** `μ` and `ν` are defined for the triadic cubes `U` resolved by the
  partition, where `cl_𝒫(U) = U` and `\|U\| = 3^{dn}`; `A_*(U)` is the space of functions on `C_*(U)`
  harmonic at the vertices of `C_*(U)` in the lattice interior of `U` (the interior of `U` for the
  lattice edges). On a cube that is not resolved `μ` is not used; `ν` is defined on every cube, through its
  crossing cluster, and its expectation is taken without an indicator (next item).
- **Locality of `ν`.** `ν(U, p)` is defined through the crossing cluster of `U` and the open edges
  inside it, hence is a local function of the configuration with exactly stationary expectation
  (`cubeNu_eq_of_equiv`, `integral_cubeNu_eq_of_scale_eq`). This replaces AD Proposition 4.9, Proposition 4.10 and
  (4.40) for `ν`. The expectation `E[ν(U, p)]` is taken without the indicator of the event that `U`
  is resolved. The quantity `μ`, which uses the anchors of the partition, is localized, and its
  stationarity and the limit of `E[−μ]` are proved, in
  [Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension](#localization-stationarity-and-the-limit-of-μ-and-definition-39-in-every-dimension).
- **Rates.** (4.49) holds with the rate `3^{−n/2}` in place of `3^{−n}`, and the lower bound (4.31)
  in expectation is proved with a deterministic slope `κ p` in place of the random one of AD, with
  the error `3^{−m/2}`.
- **Boundary error (4.27).** The paths of the cluster of the partition cubes at the faces stay in
  the crossing clusters of the partition cubes of the boundary vertices; the Hölder step uses the
  weight `W_∂` above and the moments of the partition sizes.
- **Definition 5.1.** The homogenized matrix `ā` is defined by polarization of the limit of
  `E[ν(□_m, ξ)]`, and bounded above and below by (5.1).
- **Counting convention.** AD write `⟨q, ∇[u]_𝒫⟩` as a sum over ordered pairs; the coarse pairing here
  counts each lattice edge once, as in the planar modules. The first line of AD (4.19) has a sign
  misprint: `μ(U, q) = −(1/2) ⟨∇u, a ∇u⟩_{C_*(U)}/\|U\|`.

## Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2

Lemma 5.8 (flatness of the coarsened minimizers of `μ` and maximizers of `ν`) and Lemma 5.9 (the
decay of `D_n`) of Armstrong and Dario are proved in `d = 2`, in
[`PercolationClusterHomogenization/Proofs/Percolation/`](PercolationClusterHomogenization/Proofs/Percolation/) from `PlanarFlatnessInputs.lean` to
`PlanarOmegaDecay.lean`, from the weak convergence of the spatial averages of the coarsened gradients
(Lemma 5.7, display (5.25)) and the almost additivity of these averages (Lemma 5.5, display (5.12))
alone. The proofs use the coarse energy bounds (4.24), (4.25) and the display (4.26) in `L²`, which are
proved here, not assumed. With Lemma 5.10 and `planarMuLimit_eq_of_decay` this gives the
identification `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` (the qualitative part of Proposition 5.2) with
the following three hypotheses, for `𝔭_c(2) < p < 1`:

- [`PlanarWeakConvergence`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean), display (5.25) of
  Lemma 5.7: `E[\|\|□\|⁻¹ ⟨∇[u(·, □, q)]_𝒫⟩_□ − ā_{□_n}⁻¹ q\|²] ≤ C \|q\|² (τ_n + 3^{−n/4})` for every
  triadic cube `□` of scale `n`;
- [`PlanarRestrictQuadCoarsenMu`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean) and
  [`PlanarRestrictQuadCoarsenNu`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean), display
  (5.12) of Lemma 5.5, for `n ∈ [(9/10) m, m)`, with the almost-sure measurability of the quantities
  of the display.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_coarseEnergyMu_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean), [`exists_coarseEnergyNu_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean) | AD (4.24) and (4.25), `d = 2`: for every `δ > 0` the normalized energy of the coarsened minimizer of `μ` and of the coarsened maximizer of `ν` on a cube `□` is almost surely below a measurable function of expectation at most `C(δ) \|q\|² size(□)^δ`. |
| [`sum_sq_planarNuGradAvg_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNablaAffineSq.lean), [`exists_lintegral_planarNuGradAvg_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNablaAffineMoments.lean) | AD (4.26) in `L²(P)`, `d = 2`: the spatial average of the coarsened gradient of the maximizer of `ν(V, p)` is within `C \|p\|² 3^{−n/4}`, in the second moment, of `p`. |
| [`exists_flatness_le_multiscale`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessBound.lean) | the multiscale Poincaré inequality (AD Proposition A.2) in the form of the first display of the proof of Lemma 5.8: the mean square of `w − ℓ_ξ` minus its mean is at most `C 3^{2n}(‖∇w‖² + \|ξ\|²) + C 3^m ∑_{k=n}^{m−1} 3^k (…)`. |
| [`exists_planarMuFlatness_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_lintegral_planarMuFlatness_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_planarNuFlatness_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_lintegral_planarNuFlatness_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_planarMuFlatness_majorant_ae`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessAE.lean), [`exists_planarNuFlatness_majorant_ae`](PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessAE.lean) | AD Lemma 5.8, (5.32) and (5.33), `d = 2`: `E[\|□_{n+1}\|⁻¹ ∑ \|[u]_𝒫(x) − x · ā_{□_n}⁻¹ q − c\|²] ≤ C \|q\|² 3^{2n}(3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)` and the same for `v` and `ξ`, `c` the mean; the `_ae` forms hold from Lemmas 5.7 and 5.5 alone, with an almost-sure measurable majorant. |
| [`caccioppoli_dist`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaCaccioppoli.lean), [`clusterForm_restrict_le_caccioppoli`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaCaccioppoli.lean) | AD Lemma 3.5 from `□_{n+1}` to `□_n` on planar clusters: `B_{□_n}(w, w) ≤ 16 (3^n − 1)⁻² ∑_{C_*(□_{n+1})} (w − c)²` for `w` harmonic in the interior (the Caccioppoli step (5.39) of the proof of Lemma 5.9). |
| [`planarNu_sub_planarMu_sub_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaPointwise.lean), [`planarOmega_chain`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaChain.lean), [`planarOmega_real_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaAssembly.lean), [`planarOmega_integral_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaAssembly.lean) | the pointwise chain of the proof of Lemma 5.9, (5.38) to (5.41): `ν(V, p) − μ(V, q) − q · p` is bounded by the boundary error, three times the energies of the differences of Lemma 5.4, and the Caccioppoli term in the coarsening errors and the flatness errors of Lemma 5.8, and then, summed over the subcubes, by the subadditivity gaps; its integrated form. |
| [`exists_boundaryMajorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_not_resolved_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_badMajorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_subMuSum_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_subNuSum_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_nuSubGap_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_muSubGap_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_subadditivityMajorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMajorants.lean), [`exists_coarseError_majorant`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMajorants.lean), [`planarTau_le_weighted`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaRates.lean) | the expectations of the terms of the chain: the boundary term (`C \|p\|₁ 3^{−n/2}`), the event that `□_n` is resolved and `□_{n+1}` is not (`C 9^{−n}`), the sums of `−μ` and `ν` over the subcubes by approximate stationarity, the subadditivity gaps (`C \|ξ\|₁² \|U\| 3^{−n/2}`), and the coarsening error through the reach of the partition, each with a measurable majorant, and the comparison `τ_n ≤ 3^{−n} ∑_{k ≤ n} 3^k τ_k`. |
| [`exists_planarOmegaD_le_of_inputs`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean), [`exists_planarOmegaD_decay`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Lemma 5.9, (5.37), `d = 2`, in the form used by Lemma 5.10: for `n ≥ N`, `D_n ≤ K (3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)`, that is `D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n−l} τ_l` with `σ = 3^{−1/10}` and `ρ = 1/3`, without the absolute value. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_inputs`](PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Proposition 5.2, qualitative part, `d = 2`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` from `PlanarWeakConvergence`, `PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu`; the hypothesis `h59` of `planarMuLimit_eq_of_decay` is discharged by `exists_planarOmegaD_decay`. |

The theorems of the table and their supporting results depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`; thirty-three of them (thirty theorems and three definitions,
those of the three hypotheses) have axiom reports in
[`Audit/Axioms.lean`](Audit/Axioms.lean). The remaining hypotheses of the
identification are Lemma 5.7 (`PlanarWeakConvergence`) and Lemma 5.5
(`PlanarRestrictQuadCoarsenMu`, `PlanarRestrictQuadCoarsenNu`), which are the inputs that
[Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55)
reduces to the good events of the Meyers estimate; they are not proved in this section, and are theorems
for `p > 𝔭_c(2)` in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).

Departures from Armstrong and Dario:

- **Index of the sum in (5.12).** AD print the sum `∑_{k=n}^{m+1} τ_k` in display (5.12) of
  Lemma 5.5; the last display of its proof and its use in the proof of Lemma 5.8 give
  `∑_{k=n}^{m−1} τ_k`, and the hypotheses `PlanarRestrictQuadCoarsenMu` and
  `PlanarRestrictQuadCoarsenNu` are stated with the sum over `k ∈ [n, m)`.
- **Lemma 5.7 for every cube.** `PlanarWeakConvergence` is stated for every triadic cube of scale `n`;
  AD state it for `□_n` and use it for every translate `z + □_n` by stationarity.
- **Flatness.** The flatness is measured with the mean of `w − ℓ_ξ` subtracted instead of AD's additive
  normalization of `u` and `v`; both rates in Lemma 5.8 are `3^{−n/10}` (AD print `3^{−2n/(2d+1)}` for
  `v`), which suffices for Lemma 5.9.
- **Lemma 5.9.** It is stated without the absolute value, as used in Lemma 5.10 and in the hypothesis
  `h59` of `planarMuLimit_eq_of_decay`.
- **The maximizer of `ν`.** `planarNuSolution` is the maximizer on the partition event for resolved
  cubes and `0` otherwise, a convention of this formalization (AD state `u ≡ 0` off the event, for `μ`); the
  values used agree.
- **(4.26) in `L²(P)`.** In `d = 2` the spatial average of the coarsened gradient of the maximizer of `ν` is within
  `C |p|² 3^{−n/4}` of `p` in the second moment, a weaker rate than printed; it is the rate the proof of Lemma 5.8 here uses.
- **Measurability.** Lower integrals are subadditive only for measurable summands. In the proof of
  Lemma 5.9 only one summand, the gap of `ν`, is not shown to be measurable; every other term has a
  measurable majorant, and measurability of the quantities of Lemma 5.5 is part of its hypothesis.

## Lemmas 5.5 and 5.7 in dimension two

Lemma 5.5 (display (5.12), for `μ` and for `ν`), Lemma 5.7 (display (5.25)) and the qualitative part of
Proposition 5.2 hold in `d = 2` for `𝔭_c(2) < p < 1` with no further hypothesis
([`planarRestrictQuadCoarsenMu_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarRestrictQuadCoarsenNu_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarWeakConvergence_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean),
[`planarMuLimit_eq`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean)): the three hypotheses of the
identification in the previous section are discharged, and
`lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` for every `q`.

The partition `𝓡` of Definition 3.7 is obtained from Propositions 2.1 and 2.4 applied to a local family
[`planarRHGood`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHLocal.lean). A cube is good when, on each of its
children `□`, the reverse Hölder inequality with exponent `2d/(d+1)` holds for every set of `3□`
closed under its open edges and every function harmonic on it. Its failure events are determined by
the open edges inside the threefold enlargement (hypothesis (2.1);
`measurableSet_not_mem_planarRHGood_local`). As at (3.12), its failure probability is bounded through
the planar partition: when the planar cells of `3□` have scale at most `k − 2` and
`∑ planarReach⁸ ≤ C |3□|`, the planar Lemma 3.6 holds on the cluster of the triple
(`planarRHCube_of_scales`). The parts of a closed set that no open edge leaves carry no energy, by the
Caccioppoli inequality; the parts that leave the triple meet its cluster, by the anchor property of the
planar cells. The concentration of the averages of the powers of the reach (the analogue of AD
Proposition 2.4 for the planar partition) is proved as well (`planarReachConcentration_holds`). The
hypothesis `PlanarGehringPartition`, a Gehring partition in the form used by the planar Meyers estimate,
remains only as the hypothesis of the earlier theorems `planarRestrictQuadCoarsenMu_of_gehring`,
`planarRestrictQuadCoarsenNu_of_gehring`, `planarWeakConvergence_of_gehring` and
`planarMuLimit_eq_of_gehring_partition`, which the theorems above supersede.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.measurableSet_not_mem_planarRHGood_local`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHLocal.lean) | the failure event of a cube `T` of the local family is determined by the open edges inside `3T`, as the hypothesis (2.1) of Proposition 2.1 requires. |
| [`planarRHCube_of_scales`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHEvent.lean), [`planarRHFailureBound_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHProb.lean) | the planar form of AD Lemma 3.6 on the triple of a cube whose partition cubes are small, and the failure bound (2.2) of the local family, `C exp(−c 3^{ns})`, for `p > 𝔭_c(2)`. |
| [`planarRHPartition_of_failureBound`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHPartition.lean), [`planarRHPartition_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHProb.lean) | the partition `𝓡` of AD Definition 3.7 in `d = 2`, with comparable neighbours, predecessors in the local family and, for every `t` and `B`, `∑_{x ∈ □} size(cell(x))^t ≤ K \|□\|` off an event of probability `C 3^{−Bk}` (Propositions 2.1 and 2.4). |
| [`Rigidity.Proofs.Cluster.planar_meyers_rh_uniform`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHMeyers.lean), [`meyers_triadic_uniform`](PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_uniform`](PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_clusterHarmonic_uniform`](PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`partition_meyers_uniform`](PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean) | AD Proposition 3.8, deterministic part, in the form `∃ ε t, ∀ K, ∃ C`: the exponents `ε` and `t` depend only on the reverse Hölder constant (as the minimal scale `𝓜_t(𝓡)` requires) and only the constant depends on the moment bound `K`; for the local family `planarRHGood` in `planar_meyers_rh_uniform`. |
| [`planarReachConcentration_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarReachConcentrationHolds.lean), [`Rigidity.Percolation.exists_measure_not_mem_planarCoarseGood_le`](PercolationClusterHomogenization/Proofs/Percolation/PlanarReachDomination.lean), [`planarReach_le_stoppingSize`](PercolationClusterHomogenization/Proofs/Percolation/PlanarReachDomination.lean) | the analogue of AD Proposition 2.4 for the planar partition: `∑_{x ∈ □} planarReach(x)^τ ≤ A \|□\|` off an event of probability `C 3^{−Bk}`, through the coarsely good cubes, whose failure is determined by the threefold enlargement and whose stopping size dominates the reach. |
| [`planarRestrictQuadCoarsenMu_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean), [`planarRestrictQuadCoarsenNu_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean) | AD Lemma 5.5, display (5.12), `d = 2`, `p > 𝔭_c(2)`: on the good event the deterministic bound of Step 3 applies, and off it the Cauchy–Schwarz inequality with a measurable majorant built from the moments of the reach. |
| [`Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`exists_planarNuRestrictError_majorant`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`measure_restrictBad_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictBad.lean), [`Rigidity.Percolation.measurable_planarMuRestrictError`](PercolationClusterHomogenization/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarNuRestrictError`](PercolationClusterHomogenization/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarMuGen_indicator`](PercolationClusterHomogenization/Proofs/Percolation/PlanarMuGeneral.lean) | the measurable majorants of the restriction errors, the probability of the bad event of the proof of Lemma 5.5, and the measurability of the errors (part of the hypothesis of the previous section, proved here). |
| [`Rigidity.Proofs.Cluster.exists_lintegral_sum_subcube_solenoidal_sq_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarOneVarEstBound.lean), [`exists_lintegral_planarMuRestrictFieldError_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictFieldQuad.lean) | AD Lemma 5.7, display (5.30), `d = 2`: for `n ≥ 9`, `E[\|∑_V \|□_n\|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V\|²] ≤ C \|e\|₁² \|q\|² (τ_n + 3^{−n/4})`, the sum over the subcubes `V` of scale `n` of `□_{n+1}` and `g` the solenoidal field of Step 1; the expectation of the error of the pairing of a bounded field with the coarsened gradient on `U` against its restriction to the subcubes (from the hypothesis `PlanarGehringPartition`; the same bounds with no further hypothesis, above the partition `𝓡` of `planarRHPartition_holds`, are [`exists_lintegral_sum_subcube_solenoidal_sq_le_rh`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean) and [`exists_lintegral_planarMuRestrictFieldError_le_rh`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Proofs.Cluster.exists_measure_not_planarCapGood_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_lintegral_sq_sub_switchLoc_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_variance_planarMuGradAvg_origin_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarWeakConvOrigin.lean) | AD Proposition 4.9 and Lemma 5.7, display (5.31), `d = 2`: the planar partition is determined by the edges of a neighbourhood at the cap `k`, off an event of probability at most `C (2 · 3^{n−k} + 29)² exp(−c 3^k)`; for `n ≥ 120` and `k = ⌊n/12⌋` the pairing and its local version differ in mean square by at most `C G² \|q\|₁² 3^{−n/4}`; the variance of the spatial average at the origin is at most `C \|q\|² (τ_n + 3^{−n/4})` (the last from `PlanarGehringPartition`; with no further hypothesis in [`exists_variance_planarMuGradAvg_origin_le_rh`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le_tau`](PercolationClusterHomogenization/Proofs/Percolation/PlanarDefectTauCube.lean), [`exists_lintegral_planarNuDefect_le_tau`](PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTauCube.lean) | AD Lemma 5.4, display (5.10), `d = 2`, on every triadic cube `U`: `E[1{𝒫, U resolved} D_n(U, q)] ≤ \|U\| C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})` for `μ` and for `ν`. |
| [`planarWeakConvergence_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean), [`planarMuLimit_eq`](PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean) | AD Lemma 5.7, display (5.25), for every triadic cube, and AD Proposition 5.2, qualitative part, `d = 2`, `p > 𝔭_c(2)`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q`. |

The theorems of the table and the earlier theorems from `PlanarGehringPartition` depend only on axioms among
`propext`, `Classical.choice` and `Quot.sound`; forty reports (thirty-eight theorems and two definitions)
are in [`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario:

- **The partition `𝓡`.** The good cubes ask the reverse Hölder inequality for all sets of the triple
  of each child closed under the open edges and all functions harmonic on them, not only for
  `𝒞_max(3□)` with the numerator `𝒞_*(□)` as in Definition 3.7. A cube of positive scale is good when
  the inequality holds on each of its nine children, with the energy of the closed set on the child as
  numerator; no well-connectedness is asked, and the cubes of scale zero are good. The family stays local, so that
  Propositions 2.1 and 2.4 apply to it; its failure probability is bounded through the planar
  partition, as AD bound (3.12) through the minimal scale of `𝒫`, with polynomial rates in place of
  the stretched exponentials of the tails of `𝓡`.
- **Moment exponent.** The Meyers estimate is restated with `ε` and `t` chosen before the moment
  bound `K`, the order that the minimal scale `𝓜_t(𝓡)` requires. The Lean uses
  `t = (2+ε)(1+ε)(d+1)/ε`, given by the Hölder inequality; the exponent printed at AD18.tex:1657-1663
  has a harmless factor-2 slip.
- **Lemma 5.5, Step 3.** The Hölder inequality is applied inside each cell, as in the section on the
  Meyers estimate; the cells are the triadic squares of scale `⌊n/2⌋ − 1` of the inner square, so that the
  triples and their lattice neighbourhoods lie inside the subcube, the weight is `W_t = 3 planarReach`, and
  `W = 3 √A₂ 3^k` on `U`. Off the good event the Cauchy–Schwarz inequality is used with a measurable
  majorant built from the moments of the reach; the decay is `C 3^{−Bk}`.
- **Proposition 2.4.** The concentration of the reach is proved for the planar partition through the
  coarsely good cubes (the subcubes five scales down are good; the failure of a cube is determined by
  its threefold enlargement and each subcube is ninefold local), whose stopping size dominates the reach.
- **Lemma 5.7, display (5.31).** The cap is at `k = n/12` (AD: `⌈n/2⌉`), with deterministic window bounds on
  the capped event in place of moments; the local version is the clamp to `[−M, M]` of the value at a
  configuration of the capped event with the same open edges in the neighbourhood, and `Ψ` is obtained by
  polarization of the matrix `planarMuGen` with the fields restricted to the interior (AD use `μ_loc`
  pairs on the interior). This route needs `n ≥ 120`; `n < 120` is covered by the deterministic bound, and
  every cube by translation on the local good events.

## The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two

For `𝔭_c(2) < p < 1` and with no hypothesis, the rate of convergence of the expectations in
Proposition 5.2 (display (5.4)), Lemma 5.10 (display (5.42)), Step 2 of the proof of Lemma 5.11 and a
deterministic pointwise form of Lemma 5.3 are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/). The decay of `D_n` of Lemma 5.9 holds
without the hypothesis `h59` (`exists_planarOmegaD_decay_holds`, from Lemmas 5.5 and 5.7 of the previous
section), `τ_n` and the finite-volume matrices `ā_{□_n}⁻¹` converge to `ā⁻¹` geometrically, and then
`|E[−μ(□_n, q)] − (1/2) q · ā⁻¹ q| + |E[ν(□_n, ξ)] − (1/2) ξ · ā ξ| ≤ C (|ξ|² + |q|²) 3^{−nα}` for
some `α ∈ (0, 1/4]`. The quantity `ρ = sup_q |q|⁻² ω₊` has a measurable majorant of expectation at
most `C 3^{−nα}`, its truncated stationary version has expectation at most `C (1 + C₁) 3^{−nα}`, and
sums of truncated versions over the subcubes of a cube of scale `n + 3 + j` satisfy the Chernoff
bound of Step 2. Proposition 5.2 in the `O_s` form, Steps 1 and 3 of Lemma 5.11 and
Proposition 5.13 (`p.boundN`) are not proved in this section: Step 1 of Lemma 5.11 needs a stretched
exponential tail of the minimal scale (the averages of the sizes of the cells over a cube, AD18.tex:1958
through Proposition 2.4), whereas the concentration of the partition proved here
(`planarReachConcentration_holds`, `planarRHPartition_holds`) has the polynomial tail `C 3^{−Bk}`. They are
proved in [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.exists_planarOmegaD_decay_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarOmegaD_le_geometric`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarTau_le_geometric`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.9 with no hypothesis, and the geometric decay `D_n, τ_n ≤ K l^n` for `n ≥ N`, `l < 1`. |
| [`planarAhomInvLimit_eq_inv`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.10, Step 4, `d = 2`: the limit of the finite-volume matrices is `ā⁻¹`, and `\|(ā⁻¹)_{ij} − (ā_{□_n}⁻¹)_{ij}\| ≤ K l^n` for `n ≥ N`. |
| [`planar_convexp`](PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Proposition 5.2, display (5.4), `d = 2`: there are `α ∈ (0, 1/4]` and `C` with `\|E[−μ(□_n, q)] − (1/2) q · ā⁻¹ q\| + \|E[ν(□_n, ξ)] − (1/2) ξ · ā ξ\| ≤ C (\|ξ\|² + \|q\|²) 3^{−nα}` for all `n`, `ξ`, `q`. |
| [`planar_omegadecayrate`](PercolationClusterHomogenization/Proofs/Cluster/PlanarOmegaSupRate.lean) | AD Lemma 5.10, display (5.42), `d = 2`: for each `n` there is a measurable `M`, at least `ρ(□_n) = sup_q \|q\|⁻² ω₊(□_n, q)` almost surely, with `E[M] ≤ C 3^{−nα}`. |
| [`exists_integral_min_planarRhoStat_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSIStepTwo.lean) | AD Lemma 5.11, Step 2: the truncated stationary version `ρ_stat` of `ρ` on a cube `V` satisfies `E[min(ρ_stat, C₁)] ≤ C (1 + C₁) 3^{−nα}`. |
| [`measureReal_sum_ge_le_of_bounded`](PercolationClusterHomogenization/Proofs/Cluster/BoundedChernoff.lean), [`planar_SIupgrade_step2`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSIStepTwo.lean) | the Chernoff bound of Step 2 (variables in `[0, A]` with expectations at most `ε`, each independent of the sum of any set of the others not containing it: `P[∑ ≥ \|s\| t] ≤ exp(−\|s\|(t − (e − 1)ε)/A)`), and AD Lemma 5.11, Step 2, the display at AD18.tex:3944-3947: the sum of `min(ρ_stat, C₁)` over the 729 groups of subcubes of scale `n` of a cube of scale `n + 3 + j`, `9^j` per group, exceeds `729 · 9^j t` with probability at most `729 exp(−9^j (t − (e − 1) C (1 + C₁) 3^{−nα})/C₁)`. |
| [`abs_quadratic_sub_half_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalSet.lean), [`planar_minimalset`](PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalSet.lean) | AD Lemma 5.3, `d = 2`, in a deterministic pointwise form: on the partition event for a resolved cube `U`, `\|μ(U, q) + (1/2) q · ā⁻¹ q\| ≤ (4 Y S + √(8 (Λ + 1)(ρ + Y S))) \|q\|²` and the corresponding bound for `ν(U, ā⁻¹ q) − (1/2) q · ā⁻¹ q`, with `Y` the random error of the comparison of Corollary 4.6, `Λ` the bound of `−μ`, `ρ` of Lemma 5.10 and `S` an `ℓ¹` operator bound of `ā⁻¹` (`‖ā⁻¹ v‖₁ ≤ S ‖v‖₁`); the statement assumes `Y(U) < ∞`, which holds almost surely since `E[Y] < ∞`. |

The twelve declarations of the table have axiom reports in
[`Audit/Axioms.lean`](Audit/Axioms.lean), and depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`.

Departures from Armstrong and Dario, which are choices of the formalization:

- **Display (5.4).** The `μ` part follows from the rate of `ā_{□_n}⁻¹` (Lemma 5.10, Step 4, display (5.24)); the `ν` part is obtained by
  summing the increments bounded by `τ_k` through (5.9), with `α ≤ 1/4`. AD derive (5.4) from (5.5) and Lemma 5.3.
- **Zero off the event.** `μ` and `ν` are set to `0` off the partition event and for unresolved cubes
  (AD set `u = 0` there); `ω` is then `−q · ā⁻¹ q`, so that `ω₊` and `ρ` are `0`.
- **A measurable majorant for `ρ`.** The supremum over the uncountably many `q` is not shown measurable;
  Lemma 5.10 is stated through a measurable majorant `M`.
- **The random error of Corollary 4.6.** The error `Y` of the comparison, of expectation at most `C 3^{−n/2}`, is kept random
  in Step 4 of Lemma 5.10 and in `planar_minimalset`.
- **Independence in Lemma 5.11.** Each local quantity is independent of the sums of the others only
  over pairwise disjoint local regions (of side `14 · 3^n`). The subcubes are therefore grouped by their
  position modulo `27`, and a union bound over the `729` groups replaces the single product of Step 2.
- **Lemma 5.3.** A gradient step replaces the minimizer `q₀` (so no `k(□)` is needed), and the random factor
  `√(Λ(U) + 1)` multiplies `ρ^{1/2}`; the statement is deterministic and pointwise, with the errors named.

Misprints in the source whose meaning is clear: AD18.tex:2232 (`|q|²` appears twice); :3929 (`t := 1/K` with
`K` undefined, `t = 1/C`); :3975 and :4003-4029 (`μ − (1/2) q · ā⁻¹ q` for `μ + (1/2) q · ā⁻¹ q`); :4003, :4012-4016,
:4018-4025 and :4029 (`exp(−C⁻¹ 3^{−αm})` for `exp(−C⁻¹ 3^{αm})`); :4195 (`(1/2) p · ā p + ν` for `(1/2) p · ā p − ν`).

## Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two

For `𝔭_c(2) < p < 1` and with no other hypothesis, the stretched exponential form of the convergence of
the subadditive quantities (Proposition 5.2, displays (5.2) and (5.3)), Lemma 5.11, the random scale of
Proposition 5.13 and the minimal scales of Proposition 2.4 are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/). The bounds are stated with `IsOsBond`, the
stretched exponential moment (`X ≤ O_r(θ)`) of the source, and are stable statements that the later results of
the dimension-two chain take as hypotheses
([`PlanarScaleStatements.lean`](PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleStatements.lean)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.exists_planar_minimalScale`](PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalScales.lean) | AD Proposition 2.4 for a family of cubes with the local measurability (2.1) and the failure bound (2.2): for every `τ` and `α > 0` a minimal scale `M ≤ O_r(θ)` such that, whenever `M ≤ 3^m`, the `τ`-th moment of the sizes on `□_m` is at most `K \|□_m\|` and every size is at most `3^{α m}`. |
| [`Rigidity.Proofs.Cluster.planarMinimalScales_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalScales.lean) | the statement `PlanarMinimalScales p` ([`PlanarScaleStatements.lean`](PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleStatements.lean)): the partition `𝓡` of Definition 3.7 (maximal stopping cubes of the local family `planarRHGood`), with, for all `t, α > 0`, a minimal scale `M ≤ O_r(θ)` above which on `□_m` the `t`-th moments of the sizes of the cells of `𝓡`, of the planar partition cubes and of `planarReach` are at most `K \|□_m\|` and these sizes are at most `3^{α m}`. |
| [`planarMinimalScales_partition_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleForms.lean), [`planarMesoscopicConvergence_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleForms.lean) | the two statements `Rigidity.Dirichlet.PlanarMinimalScales` and `Rigidity.Dirichlet.PlanarMesoscopicConvergence`, in the form of the inputs of the proof of Theorem 1 in dimension two: both bounds of (2.13) for the planar partition (`t ≥ 1`), and Proposition 5.13 on the triadic subcubes of `□_m` of scale `⌈m/8⌉`. |
| [`exists_measure_not_planarReachLe_le`](PercolationClusterHomogenization/Proofs/Cluster/PlanarReachEvent.lean), [`planarRho_le_avg_of_planarReachLe`](PercolationClusterHomogenization/Proofs/Cluster/PlanarReachErrors.lean), [`planarComparisonError_le_of_planarReachLe`](PercolationClusterHomogenization/Proofs/Cluster/PlanarReachErrors.lean), [`sum_subcubesAt_eq_sum_sum`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSubcubeIndex.lean) | the event that the reach is at most `3^ℓ` on a cube and the deterministic bounds on it: `-μ`, the error of the comparison of Corollary 4.6, the subadditivity errors and the subadditivity (5.56) of `ρ`; the subcubes of `□_{n+3+j}` are the cubes `⟨n, a + 27 b⟩`. |
| [`exists_planarRho_tail`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgrade.lean) | AD Lemma 5.11, Steps 1 to 3: the stretched exponential tail of `ρ(□_{n+3+j})` at an explicit threshold, together with the event that the reach is at most `3^ℓ`. |
| [`exists_planarSubaddGood_tail`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSubaddTail.lean), [`exists_planarSubaddGood_tail_cube`](PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.2 as a tail bound: `\|μ(V, q) + (1/2) q · ā⁻¹ q\| ≤ K \|q\|² 3^{−β scale V}` and `\|ν(V, ξ) − (1/2) ξ · ā ξ\| ≤ K \|ξ\|² 3^{−β scale V}` on the partition event with `V` resolved, off an event of probability at most `K' exp(−c 3^{m s})`, for `□_m` and then for every triadic cube and every translate. |
| [`planar_subadd_os`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSubaddOsMain.lean) | AD Proposition 5.2, displays (5.2) and (5.3), `d = 2`: there are `r, α, C > 0` such that, for every triadic cube `V`, the random error `X(V)` of `μ(V, ·) + (1/2) q · ā⁻¹ q` and `ν(V, ·) − (1/2) ξ · ā ξ` (with `μ = ν = 0` off the event that the partition exists and resolves `V`) is measurable with `X(V) ≤ O_r(C 3^{−α scale V})`, `\|μ-error(q)\| ≤ X \|q\|²` and `\|ν-error(ξ)\| ≤ X \|ξ\|²`. |
| [`planar_SIupgrade_os`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD Lemma 5.11, `d = 2`: `sup_q \|q\|⁻² \|ω(V, q)\| ≤ O_r(C 3^{−α scale V})`, with a measurable majorant, for every triadic cube `V`. |
| [`planar_muupbound_os`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD (4.17), `d = 2`, with the rate `size^{−α}` in place of `size^{−1}`: `−μ(V, q) ≤ (K + Z(V)) \|q\|²` with `Z(V) ≤ O_r(C 3^{−α scale V})`. |
| [`planarBoundN_holds`](PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean), [`exists_planarBoundN_general`](PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.13, `d = 2` (the statement `PlanarBoundN p`): a random scale `N ≤ O_r(θ)` such that, whenever `N ≤ 3^m` and `n = ⌈m/4⌉`, on the triadic cubes `V` of scale `n` in `□_m`, and on `□_n` in the configuration translated by `−z` for every `z ∈ □_m`, the partition event holds, the cube is resolved, and `\|μ + (1/2) q · ā⁻¹ q\| ≤ C \|q\|² 3^{−mα}`, `\|ν − (1/2) ξ · ā ξ\| ≤ C \|ξ\|² 3^{−mα}`; the second theorem allows any `n(m)` with `n(m) ≤ m ≤ L n(m)`. |
| [`osBound_indicator`](PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.add`](PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.mul`](PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`isOsBond_of_osBound`](PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean) | the calculus of the stretched exponential bounds used above, in the tail form: indicators, sums, products (AD (1.9)) and the passage to `IsOsBond`. |

The twenty-three reports of the declarations of this section and of the `O_s` calculus are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario:

- **Lemma 5.11, Step 1.** The bad event is that the reach exceeds `3^ℓ` somewhere on `□_m`, of probability
  at most `9^m · 2 exp(−3^ℓ/θ)`, with the constant `C₁ = C 81^ℓ` growing with `ℓ` and `3^ℓ ≈ 3^{nα/24}`. AD obtain a
  fixed constant `C₁` through the minimal scales ((4.17)).
- **Lemma 5.11, Step 3.** On that event the errors of the subadditivity (5.56) are bounded deterministically,
  by `C (ℓ + 1) 531441^ℓ 3^{−n/2}`, in place of an `O_s(C 3^{−k/4})` bound.
- **Proposition 5.2.** It is proved first as a tail bound and transported from `□_m` to every triadic cube and
  every translate; the `O_s` form follows from the bound `X ≤ 12 K 3^{−βm} + c (1 + M⁴) 1_{bad}`, with `M` the
  largest size of a partition cube meeting `V` and the tail calculus at the exponent `r = 1/5`. Lemma 5.11 in the
  `O_s` form is derived from Proposition 5.2, whereas AD derive Proposition 5.2 from Lemma 5.11 and Lemma 5.3.
- **Proposition 5.13.** The translates `z + □_n` are taken for every `z ∈ □_m` (AD take `z ∈ 3^k ℤ²` with
  `k = ⌈m/8⌉`), as `□_n` in the translated configuration, together with the triadic subcubes of scale `n` for the
  partition of `ω`; the scale is `N = 3 sup{3^m : the bound fails at m}`, controlled through the exponential
  moment of the exceptional scale of Lemma 2.3; and the scales are `n = ⌊m/2⌋` in Lemma 5.11 (AD take `⌈m/2⌉`).
- **Signs in Proposition 5.13.** The statement uses the signs of Proposition 5.2, `μ + (1/2) q · ā⁻¹ q` and
  `ν − (1/2) ξ · ā ξ`.

## The Dirichlet problem and the excess-decay iteration

The proof of Theorem 2 of AD compares a solution on the cluster with the solution of the homogenized
Dirichlet problem on a cube (AD, §6) and iterates this comparison over the scales to obtain the
large-scale regularity (AD, §7). The deterministic steps of both are proved, for every `d`: the
comparison of the energies and the error chain of AD, Proposition 6.1, with the inputs on the
cluster (the subadditive quantities `μ` and `ν` in every dimension and the convergence rates of
AD, §5) as hypotheses; and the iteration of AD, Lemma 7.2, with its excess-decay and
harmonic-approximation hypotheses, the excess decay being proved for the harmonic functions of
`ℤᵈ` and of the plane.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Dirichlet.innerEdgeEnergy_dirichletSolution_div_le_of_coarse`](PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixTwoCoarse.lean) | AD Lemma 6.2 on the lattice: the normalized homogenized energy of the solution `u_hom` of the discrete `ā`-Dirichlet problem on a cube `Q` of side `L`, with the boundary interpolation `w̃` of the coarsened function as datum, is at most the energy of `u` in `Q` plus the errors of the `μ` test and `C((r + N)/L)^{1−2/s}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.patch_cubeCutoff_of_not_mem`](PercolationClusterHomogenization/Proofs/Dirichlet/CutoffRegions.lean) | AD Lemma 6.3 (i) on the lattice: off the cube the patched function is the outer function. |
| [`Rigidity.Dirichlet.innerEdgeEnergy_patch_div_le_of_coarse`](PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (ii) on the lattice: the energy on the cluster of the patch `ũ` of the `ν`-maximizers and of `u_hom` is at most the homogenized energy of `u_hom` plus the boundary-layer and patching errors. |
| [`Rigidity.Dirichlet.exists_sum_sq_patch_sub_div_le_of_coarse`](PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (iii) on the lattice: `L^{−d} Σ (ũ − u_hom)²` is at most the `L²` distances of the maximizers to their affine functions plus `C N⁴ r^{−2}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.sum_abs_grad_boundaryInterpolation_rpow_div_le`](PercolationClusterHomogenization/Proofs/Dirichlet/Interpolation.lean) | AD Lemma 6.4 (iii) on the lattice: for `1 ≤ s < p`, the normalized `Lˢ` norm of `∇w̃` is at most the moments of the partition sizes times `(V⁻¹ Σ_{C_*} \|∇u 1_{𝐚≠0}\|^p)^{s/p}`. |
| [`Rigidity.Dirichlet.sum_sq_sub_le_of_inner_energy_chain`](PercolationClusterHomogenization/Proofs/Dirichlet/PropSixOne.lean) | AD Proposition 6.1 on the lattice, from the energy comparisons: if `u` is harmonic in `Q`, `ũ = u` off the interior of `Q`, `E_hom(u_hom) ≤ E(u) + δ₁` and `E(ũ) ≤ E_hom(u_hom) + δ₂`, then `Σ (u − u_hom)² ≤ 2P(δ₁ + δ₂)/λ + 2δ₃`, with `P` a Poincaré constant for `ũ − u` and `δ₃` a bound for `Σ (ũ − u_hom)²`. |
| [`Rigidity.Dirichlet.sum_energy_cubeLayer_div_le`](PercolationClusterHomogenization/Proofs/Dirichlet/LayerEnergyBound.lean) | the energy of the discrete homogenized solution in the boundary layer of width `ℓ + 1` of a cube of side `N` is at most twice that of its datum plus `C((ℓ + 1)/N)^γ (N^{−d} Σ \|∇f\|^p)^{2/p}`, for `p > 2` and small `γ > 0`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2`](PercolationClusterHomogenization/Proofs/Regularity/KIterationGeneral.lean) | AD Lemma 7.2 for every `k`, for abstract seminorms with the excess-decay hypothesis: `D_k(r) ≤ C(r/R)^{k+1} D_k(R) + C r^{1−α}(D_0(R)/R + E/r)` for `r ∈ [X ∨ C, R/2]`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero`](PercolationClusterHomogenization/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 0`: `D_0(r) ≤ C(r/R) D_0(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one`](PercolationClusterHomogenization/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 1`, with the quadratic polynomials: `D_1(r) ≤ C(r/R)² D_1(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_latticeHarmonicClass`](PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcess.lean) | the excess decay of order one of the harmonic functions on the balls of `ℤᵈ`, above a fixed radius. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_planarHarmonicClass`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularity.lean) | the excess decay of order one of the harmonic functions on the discs of `ℝ²`, in the normalized `L²` norms, with the constant `1024`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_latticeHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcess.lean) | AD Lemma 7.2 for `k = 0` with the harmonic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_latticeHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcessTwo.lean) | AD Lemma 7.2 for `k = 1` with the harmonic functions and the harmonic quadratic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularity.lean) | AD Lemma 7.2 for `k = 0` in the plane, in the normalized `L²` norms of Lebesgue measure with the harmonic functions on discs, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityTwo.lean) | AD Lemma 7.2 for `k = 1` in the plane, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_zero_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the iteration of AD Lemma 7.3 for `k = 0` in the plane, from the harmonic-approximation hypothesis. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_one_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the same for `k = 1`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_orderZero_origin_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | order-zero regularity at the origin in the plane: one constant `φ` with `‖u − φ‖_{L̲²(B_r)} ≤ C(r/R)B` for `r ∈ [X ∨ C, R/2]`, under the harmonic-approximation hypothesis. |

The nineteen theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Dirichlet/`](PercolationClusterHomogenization/Proofs/Dirichlet/) and
[`PercolationClusterHomogenization/Proofs/Regularity/`](PercolationClusterHomogenization/Proofs/Regularity/).

1. **The discrete Dirichlet problem** (`BoundaryData.lean`, `BoundaryLayer.lean`, `Hardy*.lean`,
   `WeightedEnergy.lean`, `LayerEnergy*.lean`). Existence and uniqueness, the Dirichlet principle,
   the energy identity and the maximum principle on lattice cubes, and the energy of the
   homogenized solution in a boundary layer through a Hardy-weighted energy estimate.
2. **Lemma 6.2** (`LemmaSixTwo*.lean`, `TrialEnergy*.lean`, `MuTest.lean`, `Mesoscopic*.lean`,
   `CubeTiling.lean`, `CubeStokes.lean`). The coarsened function, cut off near the boundary and
   averaged over the translates of a mesoscopic cube, is a trial function for the homogenized
   energy, compared with the energy of `u` through the `μ` test.
3. **Lemma 6.3** (`LemmaSixThree*.lean`, `Patching*.lean`, `Tile*.lean`, `AffinePatch.lean`,
   `InteriorH2.lean`, `SecondDifferences.lean`, `BoundaryCaccioppoli.lean`). The `ν`-maximizers on
   the tiles are patched along the affine approximations of `u_hom`, with the interior second
   differences of `u_hom` and the boundary-layer energy.
4. **Lemma 6.4 and Proposition 6.1** (`Interpolation.lean`, `EnergyComparison.lean`,
   `DirichletError.lean`, `PropSixOne.lean`). The boundary interpolation of the coarsened function is
   bounded by Lemmas 3.2 and 3.3, and the two energy comparisons give the `L²` error by the
   Pythagorean identity for harmonic functions.
5. **The iteration** (`BallExcess.lean`, `KIteration*.lean`, `SinglePolynomial.lean`). Lemma 7.2 is
   proved for abstract seminorms with a reverse monotonicity, Poincaré and excess-decay hypotheses,
   for every `k`, and for `k = 0, 1` in cluster, lattice and continuum instances.
6. **Excess decay** (`LatticeHarmonic*.lean`, `MixedDifferenceSobolev.lean`, `DiscreteTaylor.lean`,
   `PlanarHarmonic*.lean`). For harmonic functions on the balls of `ℤᵈ` by discrete Taylor
   expansions and Sobolev bounds of mixed differences; in the plane from the harmonic functions as
   real parts of holomorphic functions, the Borel–Carathéodory and Cauchy estimates and the
   mean-value property.

Departures from Armstrong and Dario:

- **The homogenized problem is discrete.** `u_hom` is the solution of the discrete Dirichlet problem
  for the constant conductance `ā` on the lattice cube, with the boundary interpolation `w̃` of the
  coarsened function as datum; AD use the continuum problem on the cube with a mollified datum.
  Lemma 6.4 (i) and (ii) are therefore not needed and (iv) is not used; Lemma 6.2 averages over all
  translates of the mesoscopic cube, and the energies are those of the edges inside `Q`.
- **No Meyers estimate for `u_hom`.** AD bound the boundary-layer energy of `u_hom` by the Meyers and
  `H²` estimates of AD, Proposition 6.5 (from Giusti); the Lean proof uses the interior second
  differences and a Hardy-weighted energy estimate on the lattice.
- **Lemma 6.3, Step 1.** Testing `v_y` in `μ(y + □_n, q)` gives a lower bound for the energy of
  `v_y`; the upper bound needed is obtained from the first variation of `ν` at its maximizer `v_y`,
  `E(v_y) = ⟨p, 𝐚∇v_y⟩`, so that `ν = E(v_y)/(2\|cl\|)` (`energy_le_of_nu_maximizer`).
- **Inputs on the cluster.** The `μ` test, the `ν`-maximizers and their Poincaré bounds, the
  convergence rates of AD, §5, and the Poincaré inequality for `ũ − u` enter as hypotheses.
- **Lemma 7.2.** The excess decay of `ā`-harmonic functions is proved for `ā = ½σ²I` (AD note that `ā`
  is a multiple of the identity, by the symmetries of the model): for the harmonic functions of
  `ℤᵈ`, and in the plane for the continuum norms of AD; for `d ≥ 3` the continuum excess decay is not
  proved. The harmonic approximation (AD, Lemma 7.1) and the transfer from the coarsened function to
  `u` in AD, Lemma 7.3, remain hypotheses; the general `k` follows the case `k = 0` with the excess
  over the polynomials of degree `k`, whose details AD omit, referring to Step 3 of the proof of
  Lemma 2.4 of Armstrong, Kuusi and Mourrat.

## Theorem 1 of Armstrong and Dario in dimension two

Theorem 1 of Armstrong and Dario (the homogenization error for the Dirichlet problem on the cluster of a cube)
is proved in `d = 2` for every `𝔭_c(2) < p < 1` and every exponent `p' > 2`, with no further hypothesis
([`Rigidity.Dirichlet.planarHomogenizationError_holds`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOneHolds.lean)),
in the form `PlanarHomogenizationError p p'`
([`PlanarStatements.lean`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarStatements.lean)): `ā = σ I` with `σ > 0`, and there
are `s, α, C > 0` and a measurable random scale `X ≤ O_s(C)` such that, whenever `X ≤ 3^m`, the partition event
holds, the cube `□_m` is resolved and, for every `u` harmonic on the cluster `𝒞_*(□_m)` off the boundary of the
cube, there is a discrete harmonic function `u_hom` on the lattice cube (for the constant conductance `1`) that
equals `u` on `𝒞_*(□_m)` off the interior of the cube, with
`|□_m|⁻¹ Σ_{edges of □_m} |∇u_hom|² ≤ C M²` and
`3^{−m} (|□_m|⁻¹ Σ_{𝒞_*(□_m)} (u − u_hom)²)^{1/2} ≤ C 3^{−mα} M`,
where `M = (|□_m|⁻¹ Σ_{𝒞_*(□_m)} |∇u 1_{𝐚≠0}|^{p'})^{1/p'}`. The rate is `α' = c₀/32` with
`c₀ = min(8α, 1/2, 4(1 − 2/t), 4γ)`, `t = (2 + p')/2` and `γ = min(1/16, (t − 2)/(2t))`, where `α` is the exponent of
the convergence of `μ` and `ν`.

The proof is the chain of Section 6, with the two inputs of the source in Section 5 and Section 2 supplied by
theorems:

* the convergence of `μ` and `ν` on the mesoscopic cubes, Definition 5.12, Proposition 5.13 and (6.4)–(6.5)
  (`planarMesoscopicConvergence_holds`, from
  [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two));
* the minimal scales of the planar partition, both bounds of (2.13) (`planarMinimalScales_partition_holds`, from
  the same section).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Dirichlet.planarHomogenizationError_of_inputs`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOne.lean), [`planarHomogenizationError_holds`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOneHolds.lean) | AD Theorem 1, `d = 2`, `PlanarHomogenizationError p p'` for `p' > 2`: from the two inputs `PlanarMesoscopicConvergence p` and `PlanarMinimalScales p`, and then with no hypothesis. |
| [`Rigidity.Percolation.exists_planarAhom_eq_smul_one`](PercolationClusterHomogenization/Proofs/Cluster/PlanarAhomIsotropic.lean), [`planarNuLimit_signedPermSlope`](PercolationClusterHomogenization/Proofs/Cluster/PlanarSignedPermCluster.lean) | the remark after (5.22): `ā = σ I` with `σ > 0`, from the invariance of the limit of the expectations of `ν` under the reflection and the transposition of the coordinates, which carry the planar partition, the cluster of a resolved cube and `ν` to those of the transported configuration. |
| [`Rigidity.Dirichlet.planarMu_le_test`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarMuTest.lean), [`exists_mu_test_of_subcubes`](PercolationClusterHomogenization/Proofs/Dirichlet/SubcubeMuTest.lean), [`sum_subcube_errors_le`](PercolationClusterHomogenization/Proofs/Dirichlet/SubcubeMuTest.lean) | the `μ` test of display (6.9) on a resolved subcube, the `μ` test on a translate of a mesoscopic cube from the tests on a block of its subcubes, and the sum of the errors of these tests over the translates. |
| [`planar_lemmaSixTwo`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarLemmaSixTwo.lean), [`planar_lemmaSixThree`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarLemmaSixThree.lean) | AD Lemma 6.2 (the `μ` test at every translate of the mesoscopic cube from the tests on its triadic tiles) and Lemma 6.3 (ii) (the patch of the maximizers of `ν` on the tiles), `d = 2`, with explicit errors. |
| [`planar_sum_abs_grad_boundaryInterpolation_rpow_div_le`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarInterpolation.lean), [`sum_three_pow_pairReachScale_rpow_le`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarInterpolation.lean), [`exists_planar_sum_sq_le_of_eq_zero`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarPoincareZero.lean) | AD Lemma 6.4 (iii) for the planar partition with the reach scales, the bound of the moments of the pair reach scales by the moments of the sizes of the partition cubes, and the Poincaré inequality on the cluster of a planar cube for functions vanishing on its boundary (Proposition 3.4 with `s = 2`). |
| [`planar_sum_sq_sub_uhom_le`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarPropSixOne.lean), [`planar_error_chain`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarErrorChain.lean), [`chain_le`](PercolationClusterHomogenization/Proofs/Dirichlet/PlanarChainBound.lean) | AD Proposition 6.1 in `d = 2` from Lemmas 6.2 and 6.3, the error chain `Σ_{𝒞_*} (u − u_hom)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃` with explicit errors, and its bound by a power of the tile size, `B Λ¹² L⁴ M² K^{−c₀}`. |

The seventeen reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario:

- **The homogenized solution is discrete.** `u_hom` is the solution of the discrete Dirichlet problem for the
  constant conductance `σ = ā` on the lattice cube, with the datum built from the coarsened `u` (as in
  [The Dirichlet problem and the excess-decay iteration](#the-dirichlet-problem-and-the-excess-decay-iteration)); AD
  take an `ā`-harmonic function on the continuum cube.
- **Triadic mesoscopic cubes.** The cubes are `z + □_k` with `z ∈ 3^k ℤ²` and `k = ⌈m/8⌉`, the triadic subcubes of
  `□_m`, in place of `z + □_n` with `n = ⌈m/4⌉` of Definition 5.12; Lemma 6.2 then averages the triadic tests over all
  translates.
- **The gradient bound in homogeneous form.** The bound is stated as
  `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²`, with `M` the normalized `p'`-norm of the open gradient of `u`, which is what
  Lemma 6.4 (iii) and the Dirichlet principle give.

Misprint in the source whose meaning is clear: the display (1.14) at AD18.tex:446 (`e.homogbnd`) prints on the right
side the mean of `|∇u 1_{𝐚≠0}|^p`, which is not homogeneous in `u` while the left side is quadratic.

## Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1

Lemma 7.1 of Armstrong and Dario, the harmonic approximation of the coarsening `[u]_𝒫` on the balls of the
cluster, holds in `d = 2` for `𝔭_c(2) < p < 1` with no hypothesis, and so does the order-zero regularity of
Theorem 2(iii) at `k = 0` ([`planarHarmonicApproximationTwo_holds`, `armstrongDarioOrderZeroTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean)).
The three estimates on the squares `□_j` of the proof of Lemma 7.1 (the statement `PlanarSquareEstimatesTwo p`, with
`L = 6`) are proved almost surely above one minimal scale `X ≤ O_s(θ)`, from Theorem 1
([Theorem 1 of Armstrong and Dario in dimension two](#theorem-1-of-armstrong-and-dario-in-dimension-two)) and the
minimal scales of Proposition 2.4
([Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two)):
the statements `PlanarMinimalScalesTwo p` and `PlanarHomogenizationErrorTwo p p'` of the files on Lemma 7.1 are the
statements `Rigidity.Proofs.Cluster.PlanarMinimalScales p` and `Rigidity.Dirichlet.PlanarHomogenizationError p p'`
(`planarMinimalScalesTwo_holds`, `planarHomogenizationErrorTwo_holds`).
Theorem 2(iii) at `k = 1` at the origin in dimension two follows from this and from the named hypothesis
`DarioOptimalCorrectorTwo` (Theorem 1 of Dario) alone, since `PlanarCorrectedPlaneExistenceTwo` and
`PlanarOrderOneDimensionTwo` are proved (`armstrongDarioOrderOneOriginTwo_of_dario` and
`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`; see
[Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.planarHarmonicDistTwo_of_homogenizationError`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicDistTwo.lean) | AD (7.7) on the planar squares above a minimal scale: the coarsening `[u]_𝒫` is within `C 3^{−jα} Γ_{j+3}` of a lattice harmonic function on `□_j`. The function is `u_hom` of Theorem 1 on `□_{j+1}`; its gradient is bounded by the interior estimate for the lattice Laplacian, the anchors are counted with the sizes at most `(3^{j+1})^{α'/2}`, `α' = min(α, 1)`, and the gradient norm of Theorem 1 is bounded by the Meyers estimate from `□_{j+1}` to `□_{j+2}` and the Caccioppoli inequality on `𝒞_*(□_{j+3})` (`PlanarGradNormBound`, `PlanarHarmonicComparison`, `PlanarHomogenizedGradient`). |
| [`planarCoarseComparisonTwo_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseComparisonTwo.lean), [`coarseComparison_on_square`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseComparison.lean) | AD (7.8) in the `L²` form on the planar squares above a minimal scale: `3^{−j} ‖u − [u]_𝒫‖_{L²(𝒞_*(□_j))} ≤ K Γ_{j+3}` from Lemma 3.2 with the reach scales, the Hölder inequality, the planar Meyers estimate on the cells of the minimal scales, and the Caccioppoli inequality. |
| [`planarCoarseBoundTwo_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBoundTwo.lean), [`sum_sq_coarse_sub_mean_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBound.lean), [`squareL2_coarse_sub_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBound.lean) | the bound of Step 2 of the proof of Lemma 7.1 for a constant `w = a`: the coarsened function minus its mean on `□_j` by the Poincaré inequality, Lemma 3.3 with the pair reach scales, the Meyers and Caccioppoli inequalities; and minus a constant by averaging over the cluster of the square, which carries a fixed proportion of it, with (7.8). |
| [`planarSquareEstimatesTwo_of_parts`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`planarSquareEstimatesTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | the three estimates combined into `PlanarSquareEstimatesTwo p`, with the common minimal scale the maximum of the three, and then with no hypothesis. |
| [`planarHarmonicApproximationTwo_of_inputs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`planarHarmonicApproximationTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Lemma 7.1 in dimension two, from `PlanarMinimalScalesTwo` and `PlanarHomogenizationErrorTwo` for every supercritical `p`, and then with no hypothesis. |
| [`armstrongDarioOrderZeroTwo_of_inputs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`armstrongDarioOrderZeroTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Theorem 2(iii) at `k = 0` in dimension two (`ArmstrongDarioOrderZeroTwo`), from the same inputs and then with no hypothesis. |
| [`planarPartitionSizeScale_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarPartitionSizeScale.lean) | the partition cubes of the vertices of `□_m` have scale at most `m − 2` above a minimal scale, from the minimal scales of Proposition 2.4 with `t = 1` and `α = 1/2`. |
| [`armstrongDarioOrderOneOriginTwo_of_dario`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Theorem 2(iii) at `k = 1` at the origin in dimension two (`ArmstrongDarioOrderOneOriginTwo`), from `DarioOptimalCorrectorTwo`, `PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`, by the route of the section on Lemma 7.3 at `k = 2`. |

The sixteen reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario: those of the section on order-zero regularity above (the lattice route, with
`Ā` the lattice harmonic functions and the discrete `u_hom` of Theorem 1), and the following.

- **One minimal scale.** The three estimates share the scale `X`, the maximum of the minimal scales of the three
  estimates, in the form `PlanarSquareEstimatesTwo` with `L = 6`.
- **The `L²` form of (7.8).** The comparison of `u` with `[u]_𝒫` is proved in `L²`, in place of the exponent `p'`
  of the source.

Misprint in the source whose meaning is clear: AD18.tex:5137-5146 (the squares of (7.2)), as noted in the section on
order-zero regularity above.

## Regularity of order one at the origin from the mesoscopic estimate

`Rigidity.External.ArmstrongDarioOrderOneOrigin` (Theorem 2.4, part (iii) at `k = 1`; AD Theorem 2(iii)
at `k = 1`) is a theorem from one new hypothesis and two inputs that are already assumed:
[`ArmstrongDarioMesoscopicDegreeTwo`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean), AD Lemma 7.3, display (7.18) at `k = 2`
for bond percolation at the origin, with `Ā₂` the harmonic quadratic polynomials and the normalization
`r^{−d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}`, together with `Rigidity.External.CorrectorQuantitativeInput` and
`LatticeProb.External.SupercriticalBondCorrectorInput`. The mesoscopic estimate itself needs the
harmonic approximation of AD Lemma 7.1, hence Theorem 1 (Sections 5 and 6), and is not proved in general; in
dimension two it is proved from the estimates on squares of Lemma 7.1, which are proved in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1) (see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean) | `ArmstrongDarioOrderOneOrigin` from `ArmstrongDarioMesoscopicDegreeTwo`, `CorrectorQuantitativeInput` and `SupercriticalBondCorrectorInput`. |
| [`Rigidity.Proofs.Regularity.ballExcess_le_of_clusterBallVolumeL2`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean) | the change of normalization from `r^{−d/2} ‖·‖_{L²}` to the ball excess, under the volume comparison `K` of the cluster balls, with the constant multiplied by `√K`. |
| [`Rigidity.Proofs.Regularity.orderOneEndpointData_cluster`](PercolationClusterHomogenization/Proofs/Regularity/ClusterOrderOne.lean), [`clusterLiftMap_mem_harmonicGrowthSpace`](PercolationClusterHomogenization/Proofs/Regularity/ClusterOrderOne.lean) | the hypotheses of the endpoint iteration on the cluster: the lifts of the affine functions by the corrected planes, with relative error `C t^{−1/2}` on `B_t` (absolute error `C t^{1/2}`), the trace-free quadratic polynomials, and the comparison of sizes from the density of the infinite cluster in cubes. |
| [`Rigidity.Proofs.Regularity.weighted_endpoint_step`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_step`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_iterate`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_fit`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`exists_forall_le_of_orderOneEndpoint`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean) | the endpoint iteration for abstract data: one step at the endpoint of the scale range, the product of the step factors bounded by `exp(c r^{−δ}/(1 − θ^δ))`, the fit `N_t(u − Lℓ₀) ≤ C (t/R)² N_R(u)` at each radius `t ∈ [𝒳, R/2]`, and one lifted affine function `Lℓ` for all such radii. |

`ArmstrongDarioMesoscopicDegreeTwo` is a definition of a proposition, not an axiom. The nine theorems of the
table and the definition, which have axiom reports in [`Audit/Axioms.lean`](Audit/Axioms.lean),
depend only on `propext`, `Classical.choice` and `Quot.sound`.

Departures from Armstrong and Dario:

- **The deduction of Theorem 2(iii).** AD deduce Theorem 2 from Lemma 7.3 through Proposition 3.1 of
  Armstrong, Kuusi and Mourrat, which lifts the polynomials of degree two. Here an endpoint iteration is
  used, which lifts only the affine functions, and the quadratic coefficient stays an ordinary trace-free
  quadratic polynomial; the case `k = 0` (order zero) is not used.
- **The lifts.** The affine functions are lifted by the corrected planes of slope `e_i` normalized at a vertex
  `a_0` of the cluster in `B_{X−1}` (`SupercriticalBondCorrectorInput`), with the error
  `|g_i − x_i| ≤ C t^{1/2}` from `CorrectorQuantitativeInput`, with the edge `(a_0, a_1)` in `B_X`.
  The literature proof of `CorrectorQuantitativeInput` (DG, Proposition 2.12) rests on the regularity theory of
  AD, so this route cannot later serve as a proof of that input.
- **Normalization.** The statement (7.18) is used with `|B_r| = r^d`; the Lebesgue measure
  `ω_d r^d` gives the same statement, and `Ā₂` is the space of the trace-free quadratic polynomials, as the
  homogenized matrix is a multiple of the identity.
- **The random scale.** `X = c_0 max(X_{(7.18)}, M_cube, M_corr(0), 1)` with `c_0` deterministic, and the
  exponent `s` is the minimum of the three exponents.

## Order-zero regularity and the planar corrector input from Lemma 7.1

Two reductions of the planar inputs are proved in
[`PercolationClusterHomogenization/Proofs/Regularity/`](PercolationClusterHomogenization/Proofs/Regularity/), together with deterministic steps of the proof of
AD Lemma 7.1 in dimension two. Lemma 7.1 itself, with the estimates on squares
(`PlanarSquareEstimatesTwo`), is proved in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1). The bound on the
scales of the partition cubes (`PlanarPartitionSizeScale`) follows from the minimal scales of Proposition 2.4
(`planarPartitionSizeScale_of_partCubeMoments`, see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two)).

* **Theorem 2.4 (iii) at `k = 0` in dimension two** (`ArmstrongDarioOrderZeroTwo`, AD Theorem 2(iii) at `k = 0`) from
  `PlanarHarmonicApproximationTwo`, the statement of Lemma 7.1: for `𝔭_c(2) < p < 1` there are `s, θ, A, α, K`
  and a measurable scale `X ≥ 1` with `X ≤ O_s(θ)` such that almost surely, for every `R` with `A X ≤ R` and
  every `u` harmonic on `𝒞_∞ ∩ B_R`, the coarsening `[u]_𝒫(x) = u(anchor of the planar partition cube of x)`
  satisfies the harmonic approximation against the lattice harmonic functions on the balls of `ℤ²`, and its
  `L²` comparison with `u` and with constants holds on the balls.
* **`PlanarHarmonicApproximationTwo` from the estimates on squares.**
  `planarHarmonicApproximationTwo_of_squareEstimates` derives it from `PlanarSquareEstimatesTwo p` (the
  estimate (7.7), the `L²` form of (7.8) and the bound of Step 2 for constant `w`, on the squares `□_j` above a
  minimal scale `X ≤ O_s(θ)`, for the functions harmonic on balls of `𝒞_∞`) and `PlanarPartitionSizeScale p`
  (the partition cubes of the vertices of `□_m` have scale at most `m − 2` above a minimal scale
  `M ≤ O_s(θ)`). Both are proved for `𝔭_c(2) < p < 1` (see the sections on Lemma 7.1 and on Lemma 7.3 at `k = 2`).
* **The qualitative corrector input in dimension two** (`SupercriticalBondCorrectorInputTwo`, Theorem 2.5) from `ArmstrongDarioOrderZeroTwo`,
  `PlanarCorrectedPlaneExistenceTwo` (every slope has a corrected plane on the planar infinite cluster, AD
  Theorem 2(ii) at `k = 1`, with the sublinearity in the uniform norm of the remark after (1.19), AD18.tex:527-562,
  whose conclusion is (1.22)) and `PlanarOrderOneDimensionTwo` (`dim 𝒜₁ ≤ 3`, AD Theorem 2(i) at `k = 1`).
  The last two are proved for `𝔭_c(2) < 𝔭 < 1`, so `supercriticalBondCorrectorInputTwo_holds` is the qualitative corrector input in dimension two
  with no hypothesis (see
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZeroInput.lean) | `PlanarHarmonicApproximationTwo → ArmstrongDarioOrderZeroTwo`; the other inputs it uses (the density of the infinite cluster in cubes and its concentration) are proved. |
| [`exists_planarOrderZeroDecay`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZero.lean), [`le_of_geometric_step`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZero.lean) | the Campanato iteration on the lattice balls of `𝒞_∞` that turns the harmonic approximation into the decay of the oscillation of `u`, and its elementary step. |
| [`planarHarmonicApproximationTwo_of_squareEstimates`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationTwo.lean), [`planarHarmonicApproximationAt_of_squareEstimates`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationSquares.lean), [`harmonicApproximation_of_squares`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationBalls.lean) | Lemma 7.1 in dimension two from the estimates on the squares `□_j`, by the iteration of Step 4 (`le_sum_squareIterCoeff`) and the comparison of the norms on squares and on lattice balls (`componentBallL2_le_squareL2`, `squareL2_le_componentBallL2`). |
| [`mem_clusterVertices_succ`](PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterInclusions.lean), [`mem_supp_of_mem_clusterVertices`](PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterInclusions.lean) | the inclusions of the clusters used in the proof: `𝒞_*(□_j) ⊆ 𝒞_∞` for a resolved square meeting `𝒞_∞`, and `𝒞_∞ ∩ □_m ⊆ 𝒞_*(□_{m+1})` when the partition scales on `□_m` are at most `m − 2`. |
| [`clusterRestrictTo_mem_clusterHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterRestriction.lean), [`clusterForm_clusterRestrictTo_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterRestriction.lean) | the restriction of a function harmonic on `𝒞_∞` to `𝒞_*(V)`, for a resolved `V` with `𝒞_*(V) ⊆ 𝒞_∞`, is harmonic there, and the Caccioppoli inequality from `□_{n+1}` to `□_n` for it. |
| [`supercriticalBondCorrectorInputTwo_of_orderOne`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorReduction.lean), [`eq_zero_of_slopeAsymptotics_zero`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorReduction.lean) | `ArmstrongDarioOrderZeroTwo → PlanarCorrectedPlaneExistenceTwo → PlanarOrderOneDimensionTwo → SupercriticalBondCorrectorInputTwo`, with the fact that on a cluster with the cap density the zero function determines its slope. |

The nineteen reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario:

- **The lattice route.** `Ā` is the space of the lattice harmonic functions on the balls of `ℤ²` (the discrete
  `u_hom` of the Dirichlet problem section, with `ā = σ I`), not the continuum `ā`-harmonic functions; the
  coarsening `[u]_𝒫(x)` is `u` at the anchor of the planar partition cube of `x`, with `u` extended by `0` off the
  cluster.
- **Order zero.** `ArmstrongDarioOrderZeroTwo` is obtained from the lattice form of Lemma 7.2 at `k = 0` by a
  Campanato iteration, and the transfer from `[u]_𝒫` to `u` by the iteration over the radii `A^k s`.

Misprint in the source whose meaning is clear: in the iteration of Step 4 of the proof of Lemma 7.1
(AD18.tex:5292-5316) the squares are `□_{m+3(k+1)}`, with the factor `3^{−k(m + 3(k+1)/2)}`, where
AD18.tex:5137-5146 prints `□_{m+3k}`. It does not affect Lemma 7.3.

## Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two

AD Lemma 7.3, display (7.18) at `k = 2`, is proved for planar bond percolation
(`ArmstrongDarioMesoscopicDegreeTwoPlanar`, the planar case of `ArmstrongDarioMesoscopicDegreeTwo`) from the
estimates on squares of the proof of Lemma 7.1 (`PlanarSquareEstimatesTwo`). With it,
`Rigidity.External.ArmstrongDarioOrderOneOriginTwo` (AD Theorem 2(iii) at `k = 1`, at the origin, in the plane)
is proved from `PlanarSquareEstimatesTwo`, Theorem 1 of Dario in dimension two (`DarioOptimalCorrectorTwo`),
`PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`; the estimates on squares are proved
in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1), and the last two in
[Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two),
so that only `DarioOptimalCorrectorTwo` is a hypothesis (`armstrongDarioOrderOneOriginTwo_of_dario`,
`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`). The other inputs are proved: the minimal
scales of AD Proposition 2.4 (`Rigidity.Proofs.Cluster.planarMinimalScales_holds`), which also give the
hypothesis `PlanarPartitionSizeScale` of Lemma 7.1, and the density of the infinite cluster in cubes.

The proof follows AD on the lattice. Lemma 7.2 at `k = 2` is applied to the coarsening `[u]_𝒫` on the balls of
`ℤ²`, with the lattice harmonic functions as `Ā`, the lattice harmonic quadratic functions as `Ā₂` and the
lattice harmonic cubic polynomials as `Ā₃`, up to the top scale `T = R/(8A)`; the excesses of `[u]_𝒫` are then
transferred to `u` on the cluster balls (Steps 1 and 2 of the proof of Lemma 7.3, (7.21)–(7.23)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_squareEstimates`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | `ArmstrongDarioOrderOneOriginTwo` from `PlanarSquareEstimatesTwo`, `DarioOptimalCorrectorTwo`, `PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`. |
| [`armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarHarmonicApproximationTwo_of_squareEstimates_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | (7.18) at `k = 2` in the plane, and `PlanarHarmonicApproximationTwo`, from `PlanarSquareEstimatesTwo` alone. |
| [`planarPartCubeMoments_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarPartitionSizeScale_of_partCubeMoments`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarCoarseHarmonicApproximationTwo_iff`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | the moments and the maxima of the sizes of the planar partition cubes on `□_m` above a minimal scale (part of Proposition 2.4), the bound `PlanarPartitionSizeScale` on their scales (with `t = 1`, `α = 1/2`, above `max(M, 81)`), and the identity of the two statements of Lemma 7.1 in dimension two. |
| [`mesoscopicDegreeTwoAt_of_inputs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_inputs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean) | (7.18) at `k = 2` almost surely, for one law and for every supercritical law, from Lemma 7.1 (`PlanarCoarseHarmonicApproximationTwo`) and the minimal scales of the partition cubes (`PlanarPartCubeMoments`), with `δ = α/2`; and Theorem 2(iii) at `k = 1` in the plane with the planar corrector inputs. |
| [`mesoscopicDegreeTwo_core`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoMain.lean) | (7.18) at `k = 2` for one configuration, on `[r₀X, R/2]`, from Lemma 7.1 in the form of the proof of Lemma 7.3, partition cubes of side at most `c R^{α/2}` in `B_R` whose sizes have moments of orders one and two at most `K R²`, and the density of the cluster in cubes. |
| [`coarse_top_bounds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean), [`harmonicApproximation_error_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean) | the excesses of `[u]_𝒫` over the lattice harmonic quadratic functions and over the constants at the top scale `T` bounded by the cluster excesses of `u` on `B_R` and the harmonic-approximation error at `4T`; that error bounded through the crude bound of the coarse oscillation at `R/2`. |
| [`armstrongDario_lemma_7_2_two_latticeHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeKIterationTwo.lean), [`armstrongDario_lemma_7_3_two_latticeHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeKIterationTwo.lean) | AD Lemma 7.2 at `k = 2` and its iteration for the harmonic functions on the balls of `ℤ²`, from the harmonic-approximation hypothesis alone. |
| [`harmonicRegularity_three_latticeHarmonicClass`](PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcessThree.lean), [`polynomialComparison_latticeHarmonicCubic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeCubicComparison.lean) | the excess decay of order three of the harmonic functions on the balls of `ℤ²` (harmonic third-order expansion at a corner and fourth differences), and the comparison of the excesses of the lattice harmonic cubic polynomials over the harmonic quadratic functions on two balls (third differences). |
| [`componentBallL2_le_sum_abs_of_latticeHarmonic`](PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicMeanValue.lean) | the `ℓ^∞`–`ℓ¹` bound `‖g‖_{L̲²(B_ρ)} ≤ C ρ^{−2} Σ_{B_{4ρ}} \|g\|` for `g` lattice harmonic on `B_{4ρ}`, by an absorption over boxes. |
| [`orderOneOrigin_of_mesoscopicDegreeTwoAt`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneOriginTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneOriginTwo.lean) | the reduction of Theorem 2(iii) at `k = 1` to (7.18) at `k = 2` for one dimension and one law, and its planar case. |
| [`armstrongDario_lemma_7_2_two_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityThree.lean), [`armstrongDario_lemma_7_3_two_planar`](PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityThree.lean) | AD Lemma 7.2 at `k = 2` and its iteration in the plane for the continuum norms, with the harmonic cubic polynomials as `Ā₃`. |

The twenty-one reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean); they depend only on `propext`, `Classical.choice` and
`Quot.sound`.

Departures from Armstrong and Dario:

- **The lattice route.** As for Lemma 7.1, `Ā` is the space of the lattice harmonic functions on the balls of
  `ℤ²`, and `Ā₃` is the space of the lattice harmonic cubic polynomials. The passage from the `L²` excess of
  `[u]_𝒫` to its `L¹` excess (the display after (7.19), from (7.11)) uses the `ℓ^∞`–`ℓ¹` bound of lattice
  harmonic functions.
- **The exponent.** `δ = α′/2` with `α′ = min(α, 1)` and `α` the exponent of Lemma 7.1; the
  harmonic-approximation hypothesis for `α` implies it for `α′` above the scale `1`.
- **The order of the steps.** The Lipschitz bound `D̃_0(s) ≤ C s R^{−1} D̃_0(R)` (the case `k = 0` of the same
  argument) is proved first, by an induction over the scales `s, As, A²s, …`; it bounds the coarsening error
  `K s^{−1} D̃_0(As)` of (7.8) in Step 1, for `k = 0` and `k = 2`.
- **The random scale.** `X = c₀ max(X_{L7.1}, M₁, M₂, M_cube)` with `c₀` deterministic, `M₁`, `M₂` the minimal
  scales of the moments of orders one and two of the sizes of the partition cubes with the exponent `α′/2`, and
  `M_cube` the scale of the density of the cluster in cubes.

A step of the source is repaired. After (7.19), AD18.tex:5525-5528 states
`D_k(cR) ≤ C inf_w ‖[u]_𝒫 − w‖_{L̲¹(B_{cR})}` "using (7.11)"; but (7.11) has a second term, the
harmonic-approximation error `inf_v ‖[u]_𝒫 − v‖_{L̲²}` at the top scale, which is dropped. By (7.2) that error
contains `sup_{s ∈ [Ac′R, R]} D_0([u]_𝒫; s)/s`, and the term `D_0(cR)/(cR)` of (7.19) and (7.20) is not bounded
by `D̃_0(R)/R` in Step 3 either. Here the coarse oscillations at the top scales are bounded crudely through the
largest partition cube in `B_R`, of side at most `c R^{α′/2}` above the minimal scale
(`harmonicApproximation_error_le`); the loss `R^{α′/2}` is absorbed by the factor `(4T)^{−α′}` of the
harmonic-approximation error, which leaves `δ = α′/2` in (7.18).

## Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two

For `𝔭_c(2) < 𝔭 < 1` the qualitative corrector input `SupercriticalBondCorrectorInputTwo` (Theorem 2.5, qualitative part) is proved with no further
hypothesis, in [`PercolationClusterHomogenization/Proofs/Regularity/`](PercolationClusterHomogenization/Proofs/Regularity/), by the route of Armstrong, Kuusi and
Mourrat (arXiv:1602.00512, called AKM2 here, numbered as in that paper), Proposition 3.1, Steps 3 and 4, which AD18.tex:5658
cites for Theorem 2 (i)–(iii) at `k = 1`.

* **The corrected planes** (`PlanarCorrectedPlaneExistenceTwo`, AD Theorem 2 (ii) at `k = 1`, with the sublinearity in the
  uniform norm of the remark after (1.19), AD18.tex:527-562). From the approximation of affine functions on the balls
  `B_{3^m}` of the cluster by harmonic functions `u_m` with `‖u_m − q·x‖ ≤ K |q|₁ 3^{m(1−δ)}`
  (`PlanarAffineApproximationAeTwo`), the corrector of the slope `q` is the diagonal limit of the `u_m`, by the telescoping
  bound and the Lipschitz estimate at the origin of the order-zero regularity (`exists_harmonic_of_approximations`, Step 3 of
  AKM2 Proposition 3.1). This gives (1.18), `|χ_q|` in `L̲²(𝒞_∞ ∩ B_r)` at most `C |q| r^{1−δ}` above a scale, with the scale
  almost surely finite (`PlanarCorrectorSublinearL2AeTwo`), and then the bound in the uniform norm
  (`abs_corrector_le_at_scale`, `componentSlopeAsymptotics_of_scales`).
* **The approximation of affine functions** (`planarAffineApproximationAeTwo_of_minimalScales`) by the maximizers of `ν`:
  `u_m = q₀ v(·, □_{j+3}, e₀) + q₁ v(·, □_{j+3}, e₁) − c` on `B_{3^{j+1}}`, with the bound on the energy of `ν`
  (`clusterForm_planarNuSolution_le`, `ν ≤ (9/4)|ξ|₁²`), the coarsening errors by Lemma 3.2 with reach scales at most the
  scale `D` (`sum_sq_extend_sub_coarsen_le`), the flatness of the combination (`sum_sq_coarsen_combo_le`), and (5.33)
  (AD18.tex:3413), proved from Lemmas 5.5 and 5.8, in expectation, with the geometric decay of `τ_n` from Lemma 5.10; all are
  proved in the sections on those lemmas above.
* **`dim 𝒜₁ ≤ 3`** (`planarOrderOneDimensionTwo_of_mesoscopic`, AD Theorem 2 (i) at `k = 1`), from (7.18) at `k = 2` of
  Lemma 7.3 (AD18.tex:5490-5497), the density of the cluster in cubes and the existence of the corrected planes: for one
  configuration, every `u ∈ 𝒜₁` is `a + Σᵢ ξᵢ gᵢ` for the corrected planes `gᵢ` of slopes `eᵢ`
  (`eq_clusterLiftMap_of_orderOne`, Step 4 of AKM2 Proposition 3.1), so `𝒜₁` lies in the range of a linear map from
  `ℝ × ℝ²`.
* **The inputs are discharged in dimension two** (`Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean`). The statement
  `MesoscopicDegreeTwoPlanarInput` used for the dimension is `ArmstrongDarioMesoscopicDegreeTwoPlanar` (by `Iff.rfl`,
  `mesoscopicDegreeTwoPlanarInput_iff`), and (7.18) at `k = 2` follows from the estimates on squares
  (`mesoscopicDegreeTwoPlanarInput_holds`, from `planarSquareEstimatesTwo_holds`); the minimal scales are
  `planarMinimalScalesTwo_holds` and the order-zero regularity `armstrongDarioOrderZeroTwo_holds`. Hence
  `planarCorrectedPlaneExistenceTwo_holds`, `planarOrderOneDimensionTwo_holds`, `supercriticalBondCorrectorInputTwo_holds`,
  `supercriticalBondGreenColumnExistenceTwo_holds` (by `supercriticalBondGreenColumnExistenceTwo_of_correctorInput`), and
  `armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector` from `DarioOptimalCorrectorTwo` alone. There is no circularity: (7.18)
  at `k = 2` uses the estimates on squares, not the corrector estimate.
  `darioOptimalCorrectorTwo_of_oscillation` is Theorem 1 of Dario with the qualitative corrector input and the order-zero regularity discharged.

| Lean declaration | Statement |
| --- | --- |
| [`exists_planar_all_centres_constant_approximation`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorL2.lean), [`ae_eventually_scale_le_three`](PercolationClusterHomogenization/Proofs/Regularity/PlanarScaleMaxima.lean) | the order-zero approximation by constants at every centre of the ball, and the almost sure bound of the minimal scales over the triadic boxes at all large scales. |
| [`abs_corrector_le_at_scale`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupNorm.lean), [`componentSlopeAsymptotics_of_scales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupNorm.lean), [`planarCorrectedPlaneExistenceTwo_of_sublinearL2`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectedPlaneExistence.lean), [`supercriticalBondCorrectorInputTwo_of_sublinearL2`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectedPlaneExistence.lean) | the corrector bounded uniformly on a box by powers of the minimal scale, from (1.18) and the Lipschitz estimate; the sublinearity in the uniform norm; the corrected planes and the qualitative corrector input from (1.18) with an almost surely finite scale. |
| [`exists_harmonic_of_approximations`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorConstruction.lean), [`planarCorrectorSublinearL2Two_of_affineApproximation`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean), [`planarCorrectedPlaneExistenceTwo_of_affineApproximation`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean), [`planarCorrectedPlaneExistenceTwo_of_affineApproximationAe`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean) | Step 3 of AKM2 Proposition 3.1: the harmonic function on the cluster from approximations on growing balls, (1.18), and the corrected planes. |
| [`clusterForm_planarNuSolution_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`sum_sq_extend_sub_coarsen_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`sum_sq_coarsen_combo_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`affineApproximation_at_scale`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`radicand_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean) | the energy of the maximizers of `ν` and of their combinations, their coarsening errors, and the approximation of affine functions at one scale. |
| [`ae_eventually_planarNuFlatness_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarNuFlatnessAS.lean), [`planarAffineApproximationAeTwo_of_nuFlatness`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`planarCorrectedPlaneExistenceTwo_of_nuFlatness`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`planarAffineApproximationAeTwo_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationHolds.lean), [`planarCorrectedPlaneExistenceTwo_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationHolds.lean) | the Markov inequality and the Borel–Cantelli lemma for the flatness (5.33) in expectation, giving an almost sure bound at all large scales; the approximation of affine functions with an almost surely finite scale; the corrected planes from the minimal scales and the order-zero regularity. |
| [`eq_clusterLiftMap_of_orderOne`](PercolationClusterHomogenization/Proofs/Regularity/OrderOneLift.lean), [`planarOrderOneDimensionTwo_of_mesoscopic`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneDimension.lean), [`planarOrderOneDimensionTwo_of_minimalScales`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneDimension.lean), [`supercriticalBondCorrectorInputTwo_of_mesoscopic`](PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderOneDimension.lean) | Step 4: every element of `𝒜₁` is a constant plus a combination of corrected planes; `dim 𝒜₁ ≤ 3`; the qualitative corrector input from (7.18) at `k = 2`, the minimal scales and the order-zero regularity. |
| [`mesoscopicDegreeTwoPlanarInput_iff`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`mesoscopicDegreeTwoPlanarInput_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`planarCorrectedPlaneExistenceTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`planarOrderOneDimensionTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`supercriticalBondCorrectorInputTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`supercriticalBondGreenColumnExistenceTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`darioOptimalCorrectorTwo_of_oscillation`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean) | (7.18) at `k = 2`, the corrected planes, `dim 𝒜₁ ≤ 3`, the qualitative corrector input and the Green columns in dimension two with no hypothesis beyond `𝔭_c(2) < 𝔭 < 1`; Theorem 2 (iii) at `k = 1` at the origin from `DarioOptimalCorrectorTwo` alone; Theorem 1 of Dario from the multiscale Poincaré inequality, the concentration inequality, (1.22) and Lemma 3.3. |

The thirty-two reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario and from Armstrong, Kuusi and Mourrat:

- **The scale of (1.18) is almost surely finite, not `O_s`.** The flatness (5.33) is proved in expectation only. The Markov
  inequality gives `P[Φ_n ≥ (|ξ|² + 1) 9ⁿ μⁿ] ≤ C B (n + 1) μⁿ` with `μ = μ₁^{1/2}`
  (`ae_eventually_planarNuFlatness_le`), a scale with a polynomial tail, and the Borel–Cantelli lemma over
  the scales (with `τ_n ≤ K l^n`) gives a scale that is almost surely finite. This is enough for the qualitative statements
  (corrected planes, sublinearity in the uniform norm, `dim 𝒜₁ ≤ 3`) but not for the quantitative statements (1.18) and (1.22)
  with `O_s` scales. These are proved by a second route, with Lemma 5.5 and the subadditivity defect in place of `τ_k`, in
  [The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two).
- **Step 4 of AKM2 Proposition 3.1 without orthogonality.** AKM2 uses the orthogonality of the `ā`-harmonic monomials to
  lift `𝒜₁`. Here the endpoint iteration of the order-one regularity gives, for each radius `R`, one lifted affine function
  `ℓ_R` with error `C (t/R)² ‖u‖_R = o(1)` for `u ∈ 𝒜₁`; the sizes of `ℓ_R` are bounded, and a limit point `ℓ` gives
  `u = Lℓ`. Only the qualitative statement that each `eᵢ` has a corrected plane is used, so the scale is almost surely finite.
- **Step 3 of AKM2 Proposition 3.1 and the remark after (1.19).** The Lipschitz estimate is used in the form of the order-zero regularity (`k = 0`) at the
  centre, Borel–Cantelli over the triadic boxes replaces the stochastic integrability, and the sublinearity in the uniform
  norm uses a staircase interpolation on `x + [0, t]²`.
- **The lattice route.** The harmonic functions in the approximation are on the balls of the cluster, and the approximation
  uses the maximizers of `ν` on `□_{j+3}` (AD Lemma 5.8 (5.33) and Lemma 5.10 in place of the energy of the continuum
  corrector), with reach at most `3^{(j+3)/4}` from the minimal scales with `α = 1/4`.

## The quantitative sublinearity of the correctors in dimension two

For `𝔭_c(2) < 𝔭 < 1` the bound (1.18) of Armstrong and Dario (`PlanarCorrectorSublinearL2Two`) and the quantitative
sublinearity (1.22) in the oscillation form (`PlanarCorrectorOscSublinearTwo`, which is the statement
`CorrectorOscSublinearTwo` of [Theorem 1 of Dario in dimension two](https://github.com/nitromannitol/Percolation-Rigidity#theorem-1-of-dario-in-dimension-two) by `Iff.rfl`,
`planarCorrectorOscSublinearTwo_iff`) are proved with minimal scales of class `O_s` and no further hypothesis, in
[`PercolationClusterHomogenization/Proofs/Regularity/`](PercolationClusterHomogenization/Proofs/Regularity/).

* **(5.33) of Lemma 5.8 above a minimal scale of class `O_s`** (`exists_planarNuFlatness_os`), from Proposition 5.2 for
  `ν` in the form `O_s` (`PlanarNuSubaddOsTwo p`). For one configuration, the flatness error of the coarsened maximizer
  of `ν(□_{n+1}, eᵢ)` is bounded by the reach, the subadditivity errors of `ν` and the constant of Lemma 5.5
  (`exists_planarFlatness_le_of_reach`): Lemma 5.5 is applied off its bad event, with the energy of the differences of the
  maximizers bounded by the subadditivity errors in place of `τ` (`planarNuDefect_le_of_errors`), the exceptional vertices
  counted by the reach, and the coarse energy and (4.26) bounded with the reach at most `(3^{n+1})^{1/40}`. This bound is
  at most `2 · 9ⁿ μⁿ` for some `μ < 1` and all large `n` (`exists_flatnessBound_le`). The bad event of Lemma 5.5 lies
  almost surely in a measurable event on the stopping sizes of the coarsely good and reverse Hölder partitions, of
  stretched-exponential probability (`exists_restrictBad_os`); with union bounds over the vertices, the subcubes and the
  scales, the exceptional event at the scale `n` has probability at most `C exp(−c 3^{nσ})`
  (`exists_measure_flatnessBad_le`), and the supremum of the `3ⁿ` on these events is of class `O_s`
  (`exists_isOsBond_of_events`).
* **(1.18) with a minimal scale of class `O_s`** (`planarAffineApproximationTwo_of_subaddOs`,
  `planarCorrectorSublinearL2Two_of_subaddOs`): the approximation of affine functions and the construction of the
  correctors of
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two),
  with (5.33) above this minimal scale.
* **(1.22)** (`planarCorrectorOscSublinearTwo_of_sublinearL2`). The correctors `u₀, u₁` of the slopes `e₀, e₁` are bounded
  on the boxes of side `2N`, `N = 9 · 3^m`, by `C (3^m)^{1−7η}` above a minimal scale of class `O_s`
  (`exists_corrector_sup_os`, with the local minimal scales on the triadic boxes, `exists_isOsBond_scale_le_three`); a
  corrected plane of slope `q` is a constant plus `q₀ u₀ + q₁ u₁`, by the Liouville theorem of order zero
  (`eq_add_of_isCorrectedPlane`); and `Z_R = 2 (C + 1) max(R, 9 max(X, 1))^{1−7η}` is at most
  `18 (C + 1) R^{1−7η} max(X, 1)`, of class `O_s(C R^{1−δ})`.
* **The inputs are discharged** (`PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean`). `PlanarNuSubaddOsTwo p` is
  the part on `ν` of Proposition 5.2 (`planar_subadd_os`, `planarNuSubaddOsTwo_holds`), the minimal scales are
  `planarMinimalScalesTwo_holds` and the order-zero regularity is `armstrongDarioOrderZeroTwo_holds`. Hence
  `planarAffineApproximationTwo_holds`, `planarCorrectorSublinearL2Two_holds` and `planarCorrectorOscSublinearTwo_holds`.
  With (1.22), Lemma 3.2 of Dario holds with no hypothesis (`darioLemmaThreeTwo_holds`, by `darioLemmaThreeTwo_of_osc`, in
  `Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean`), and Theorem 1 of Dario in dimension two and the quantitative
  corrector input of Dario and Gu (Proposition 2.12) follow from the multiscale Poincaré inequality, the concentration
  inequality and Lemma 3.3 of Dario (`darioOptimalCorrectorTwo_of_lemmaThreeThree`,
  `correctorQuantitativeInputTwo_of_lemmaThreeThree`). There is no circularity: the route uses Proposition 5.2, the
  minimal scales and the order-zero regularity, not the corrector estimate of Dario.

| Lean declaration | Statement |
| --- | --- |
| [`exists_isOsBond_of_events`](PercolationClusterHomogenization/Proofs/Regularity/PlanarStretchedScales.lean), [`exists_restrictBad_os`](PercolationClusterHomogenization/Proofs/Regularity/PlanarRestrictErrorOs.lean), [`planarNuDefect_le_of_errors`](PercolationClusterHomogenization/Proofs/Regularity/PlanarRestrictErrorOs.lean) | a minimal scale of class `O_s` from events of stretched-exponential probability; the bad event of Lemma 5.5 inside a measurable event of stretched-exponential probability; the energy of the differences of the maximizers of `ν` bounded by the subadditivity errors. |
| [`exists_planarFlatness_le_of_reach`](PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessPathwise.lean), [`exists_flatnessBound_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessDecay.lean), [`exists_measure_flatnessBad_le`](PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessOs.lean), [`exists_planarNuFlatness_os`](PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessOs.lean) | the flatness error (5.33) for one configuration by its reach and the subadditivity errors, its decay, the probability of the exceptional event at each scale, and (5.33) above a minimal scale of class `O_s`. |
| [`planarAffineApproximationTwo_of_subaddOs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationOs.lean), [`planarCorrectorSublinearL2Two_of_subaddOs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationOs.lean) | the approximation of affine functions and (1.18) with minimal scales of class `O_s`, from Proposition 5.2 for `ν` in the form `O_s`, the minimal scales and the order-zero regularity. |
| [`exists_isOsBond_scale_le_three`](PercolationClusterHomogenization/Proofs/Regularity/PlanarLocalScalesOs.lean), [`exists_corrector_sup_os`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupOs.lean), [`eq_add_of_isCorrectedPlane`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOsc.lean), [`planarCorrectorOscSublinearTwo_of_sublinearL2`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOsc.lean), [`planarCorrectorOscSublinearTwo_of_subaddOs`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOsc.lean) | the local minimal scales on the triadic boxes, the bound of the correctors on the boxes, the corrected planes as combinations of `u₀, u₁`, and (1.22) from (1.18) and from Proposition 5.2 for `ν` in the form `O_s`. |
| [`planarNuSubaddOsTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorOscSublinearTwo_iff`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarAffineApproximationTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorSublinearL2Two_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorOscSublinearTwo_holds`](PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorOscHolds.lean) | Proposition 5.2 for `ν` in the form `O_s`, the identity of the two statements of (1.22), and the approximation of affine functions, (1.18) and (1.22) with no hypothesis beyond `𝔭_c(2) < 𝔭 < 1`. |
| [`Rigidity.Corrector.correctorOscSublinearTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`darioLemmaThreeTwo_holds`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`darioOptimalCorrectorTwo_of_lemmaThreeThree`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`correctorQuantitativeInputTwo_of_lemmaThreeThree`](https://github.com/nitromannitol/Percolation-Rigidity/blob/main/Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean) | (1.22) in the form used by Dario, Lemma 3.2 of Dario with no hypothesis, and Theorem 1 of Dario and Proposition 2.12 of Dario and Gu from the multiscale Poincaré inequality, the concentration inequality and Lemma 3.3. |

The twenty-three reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean).

Departures from Armstrong and Dario:

- **(5.33) in the form `O_s`.** Lemma 5.5 and (5.33) of Lemma 5.8 are printed in expectation (AD18.tex:2936-2950,
  AD18.tex:3402-3418). The form above a minimal scale of class `O_s` is assembled from printed ingredients: the pathwise
  inequalities of the proof of Lemma 5.5, Proposition 5.2 in the form `O_s` and the minimal scales of Proposition 2.4. The
  energy of the differences of the maximizers is bounded by the subadditivity errors, not by `τ_k`, and the exceptional
  vertices are counted by the reach.
- **(1.22) from the uniform bound.** The bound in the uniform norm of the remark after (1.19) is proved with a minimal
  scale of class `O_s` by a union bound over the triadic boxes, with the Lipschitz estimate in the form of the order-zero
  regularity at the centre, and the corrected planes of every slope are reduced to those of `e₀, e₁` by the Liouville
  theorem of order zero. The exponent obtained is `R^{1−δ/4}` (`7η = δ/4`, with `δ = min(δ₁, 1)` for the exponent `δ₁`
  of (1.18)), against `r^{1−δ/2}` in the remark after (1.19) (AD18.tex:554-559). This does not affect the statement,
  which asks only for some `δ ∈ (0, 1]`.

## The subadditive quantities of Armstrong and Dario in every dimension: Lemmas 5.3 and 5.4, (5.21) to (5.24) and Step 1 of Lemma 5.10

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the following are proved in [`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/)
(namespace `Rigidity.Percolation`; the files `GeneralSlopeQuadratic`, `GeneralMinimalSet`, `GeneralMuEnergyDefect`,
`GeneralTauIncrements` and `GeneralFiniteVolumeMatrix`), with the quadratic forms in the slope handled by the polarization
identity (`IsSlopeQuadratic`) and by the cube quantities `cubeMu`, `cubeNu` and `cubeAhom` of the previous sections.

| Lean declaration | Statement |
| --- | --- |
| [`abs_slopeQuadratic_sub_half_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean), [`IsSlopeQuadratic.le_of_nonneg`](PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean), [`IsSlopeQuadratic.comp_mulVec`](PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean) | the deterministic gradient step behind Lemma 5.3, and the closure of slope quadratic forms under sums and linear changes of the slope. |
| [`sum_mul_le_neg_cubeMu_add_cubeNu_add_mul`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMinimalSet.lean) | the homogeneous form of Corollary 4.6, (4.29): `q · ξ ≤ −μ(U, q) + ν(U, ξ) + \|q\|₁ \|ξ\|₁ Y(U)`, with `Y(U) = cubeComparisonError`. |
| [`cube_minimalset`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMinimalSet.lean) | AD Lemma 5.3, (5.6), on resolved cubes, in every dimension. |
| [`exists_lintegral_cubeMuDefect_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuEnergyDefect.lean) | AD Lemma 5.4, (5.10), for `μ`, before summing the increments: `E[D^μ_n(U)] ≤ \|U\| (E[−μ(W)] − E[−μ(U)] + C \|q\|₁² (3^{−n/4} + exp(−c 3ⁿ)))`, `W` of scale `n ≤` that of `U`. |
| [`exists_lintegral_cubeMuDefect_le_tau`](PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`exists_lintegral_cubeNuDefect_le_tau`](PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean) | AD Lemma 5.4, (5.10), for `μ` and for `ν`: `E[D_n(□_m)]/\|□_m\| ≤ C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})`. |
| [`exists_cubeMuIncrement_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`exists_cubeNuIncrement_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`summable_cubeTau`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the increments (5.9) for `μ` and for `ν`, and the summability of `τ_k`. |
| [`cubeAhomInvFinite`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`half_sum_mul_cubeAhomInvFinite_eq`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the matrix `ā_n^{−1}` of (5.21) and its defining identity. |
| [`exists_cubeAhomInvFinite_bounds`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the bounds (5.22): for `n` at least some `N`, `c \|q\|² ≤ ½ q · ā_n^{−1} q ≤ C \|q\|²`. |
| [`integral_cubeCoarsePairing_cubeMuMinimizer`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeCoarsePairing_cubeMuMinimizer_div`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | (5.23): the expectation of the pairing of the coarse gradient at `q'` with the minimizer at `q`, divided by the volume, on the resolved cube of scale `n`, is `q' · ā_n^{−1} q`. |
| [`exists_abs_cubeMuMean_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`exists_abs_cubeAhomInvFinite_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`exists_abs_cubeAhomInvLimit_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`tendsto_cubeAhomInvFinite`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | (5.24): `\|E[−μ(□_n, q)] − E[−μ(□_m, q)]\| ≤ C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})`, the same bound entrywise for `ā_n^{−1}` and `ā_m^{−1}`, and for `ā_n^{−1}` and its limit with `∑_{k ≥ n} τ_k`. |
| [`exists_cubeAhomInvFinite_mul_cubeAhomFinite`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeMuMean_cubeAhomFinite_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeOmegaD_succ_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | `ā_n^{−1}` is invertible from some scale on, `x ↦ E[−μ(□_n, x)] − ξ · x` is minimal at `x = ā_n ξ`, and the first part of Step 1 of Lemma 5.10: `D_{n+1} ≤ D_n` minus the increments of `E[ν]` at the unit vectors and of `E[−μ]` at `ā_n e_i`. |

The thirty-five reports for the declarations of this section are in [`Audit/Axioms.lean`](Audit/Axioms.lean).
The second part of Step 1 of Lemma 5.10 and the rest of Lemma 5.10, Lemmas 5.5, 5.7, 5.8, 5.9 and 5.11 and Proposition 5.2
are not yet proved in every dimension; in dimension two they are proved in the planar sections above.

Departures from Armstrong and Dario:

- **Lemma 5.3** is stated deterministically on resolved cubes, with a gradient step in place of the minimizer `q₀` (no
  `k(□)`), and the random factor `√(Λ + 1)` on `ρ^{1/2}`, as in dimension two; the tails of `Y` and `Λ` are not part of the statement.
- **(4.29)** is used with Young's parameter chosen for each slope, giving the error `|p|₁ |q|₁ Y(U)`.
- **Lemma 5.4**: the forms with `τ_k` are stated for the cube at the origin only.
- **Lemma 5.4** for `ν` is stated at the slopes `ā^{−1} q` (Armstrong and Dario state it for every slope; the two are equivalent
  since `ā = σ I` with `σ > 0`). For `μ` the energy is on the clusters `𝒞_*(V)`, as in dimension two, with the rate `3^{−n/4}` of
  (4.32) in expectation and the term `exp(−c 3ⁿ)` from the approximate stationarity of `E[−μ]`.

## Section 3 and the isotropy of the homogenized matrix in every dimension

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, with no further hypothesis, the partition `𝓡` of Definition 3.7 of Armstrong and
Dario, the Meyers estimate of Proposition 3.8 above it, and the isotropy of the homogenized matrix are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/) (namespace `Rigidity.Proofs.Cluster.GeneralDim` for
`GeneralRHLocal`, `GeneralRHEvent`, `GeneralRHProb`, `GeneralRHPartition` and `GeneralRHMeyers`, and
`Rigidity.Percolation` for `GeneralRHExit`, `GeneralReachDomination` and `GeneralAhomIsotropic`). The construction is that of the planar section
[Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two) in every dimension: Propositions 2.1 and 2.4 are
applied to a local family of cubes, the cubes on whose children the reverse Hölder inequality holds, whose failure is
bounded through the partition into good cubes.

* **The local family** (`rhGood`, from `RHCube`, the reverse Hölder inequality with exponent `2d/(d+1)` for every set of
  the triple closed under the open edges and every function harmonic on it): its failure events are determined by the open
  edges of the threefold enlargement, the hypothesis (2.1) of Proposition 2.1 (`measurableSet_not_mem_rhGood_local`).
* **Lemma 3.6, deterministic part** (`rhCube_of_scales`): a cube whose triple has partition cubes of scale at most `k − 2`
  and `∑_{3□} partitionReach^{2d(d+2)} ≤ C_G 3^{(k+1)d}` is a reverse Hölder cube. A vertex joined by an open path to the
  boundary of the box of its partition cube is joined to its anchor inside the parent of the partition cube and the box
  (`reachable_partitionAnchor_of_exit`, `mem_partitionBoxCluster_of_exit`), and a part of a closed set that no open edge
  leaves carries no energy (`clusterGradSq_eq_zero_of_closed`).
* **The failure bound (2.2)** (`rhFailureBound_holds`): the scale tail of the partition cubes, the stretched exponential
  concentration of the reach on a triple (`exists_measure_sum_reach_enl_gt_le`, with the exponent `1/(2(d + 2d(d+2) + 1))`),
  and Lemma 3.6. The reach of the partition is dominated by the stopping size of the partition into coarsely good cubes,
  whose failure events are local and of probability at most `C exp(−c 3^n)`
  (`partitionReach_le_stoppingSize_coarseGood`, `exists_measure_not_mem_coarseGood_le`, Lemma 2.7).
* **The partition `𝓡`** (`rhPartition_holds`): the maximal stopping cubes of the local family form almost surely a partition
  with comparable neighbours, every predecessor of a cell is in the local family, and for every exponent the moments of the
  sizes of the cells over a triadic cube are at most `K |□|` off an event of probability `C 3^{−Bk}`
  (`rhPartition_of_failureBound`).
* **Proposition 3.8 above `𝓡`** (`meyers_rh_uniform`): the Meyers estimate with exponents `ε, t` depending only on the
  reverse Hölder constant, for every set `U₀` closed under the open edges inside the triple `3□`
  (`avg_clusterEnergy_le_of_rhGood`, with the constant `3^{d+1} max(1, A₀)`).
* **Isotropy** (`exists_cubeAhom_eq_smul_one`, `Rigidity.Percolation`): `ā = σ I` with `σ > 0`, for `d ≥ 2` and
  `𝔭_c(d) < p < 1` (the remark after (5.22) of Armstrong and Dario). The signed permutations of `ℤ^d` carry crossing
  clusters to crossing clusters and leave `ν`, its expectations on the cube at the origin and their limit invariant
  (`cubeNu_signedPerm`, `cubeNuLimit_signedPermSlope`); only the crossing cluster is used, since the rounded three-quarter
  cubes of the good cubes are not reflection-symmetric, so no goodness is needed.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.GeneralDim.measurableSet_not_mem_rhGood_local`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHLocal.lean) | the failure event of a cube of the local family `rhGood` is determined by the open edges of the threefold enlargement, as the hypothesis (2.1) of Proposition 2.1 requires. |
| [`rhCube_of_scales`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHEvent.lean), [`mem_partitionBoxCluster_of_exit`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHEvent.lean), [`Rigidity.Percolation.reachable_partitionAnchor_of_exit`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHExit.lean) | AD Lemma 3.6, deterministic part, in every dimension, in the form of a reverse Hölder cube for every closed set of the triple, with the exit lemma that joins a vertex to its anchor. |
| [`Rigidity.Percolation.partitionReach_le_stoppingSize_coarseGood`](PercolationClusterHomogenization/Proofs/Cluster/GeneralReachDomination.lean), [`exists_measure_not_mem_coarseGood_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralReachDomination.lean), [`Rigidity.Proofs.Cluster.GeneralDim.exists_measure_sum_reach_enl_gt_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHProb.lean) | the reach of the partition into good cubes is at most the stopping size of the partition into coarsely good cubes, the failure bound of the coarsely good cubes (Lemma 2.7), and the concentration of the sums of the powers of the reach on a triple. |
| [`rhFailureBound_holds`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHProb.lean), [`rhPartition_holds`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHPartition.lean) | the failure bound (2.2) of the local family and the partition `𝓡` of Definition 3.7 with its minimal scales (Propositions 2.1 and 2.4), `d ≥ 2`, `p > 𝔭_c(d)`. |
| [`meyers_rh_uniform`](PercolationClusterHomogenization/Proofs/Cluster/GeneralRHMeyers.lean) | AD Proposition 3.8 above the partition `𝓡`, in every dimension, with `ε` and `t` depending only on the reverse Hölder constant. |
| [`Rigidity.Percolation.cubeNu_signedPerm`](PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean), [`cubeNuLimit_signedPermSlope`](PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean), [`exists_cubeAhom_eq_smul_one`](PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean) | the invariance of `ν` and of the limit of its expectations under the signed permutations of the coordinates, and `ā = σ I` with `σ > 0` in every dimension `d ≥ 2`. |

The thirteen reports for the declarations of this section are in
[`Audit/Axioms.lean`](Audit/Axioms.lean). Definition 3.9 (the partition `𝓠_a` for the Meyers
estimate) and the localization of `μ` are proved in
[Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension](#localization-stationarity-and-the-limit-of-μ-and-definition-39-in-every-dimension).

Departures from Armstrong and Dario: the good cubes of the local family ask the reverse Hölder inequality for all sets of
the triple of each child closed under the open edges and all functions harmonic on them, not only for `𝒞_max(3□)` with the
numerator `𝒞_*(□)`; the failure probability is bounded through the partition into good cubes with polynomial rates in
place of the stretched exponentials of the tails of `𝓡`, as in the planar section.

## Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the localization of the partition and of `μ` (Propositions 4.9 and 4.10),
the locality (4.39) and stationarity (4.40), the subadditivity error (4.32) in expectation, the approximate
monotonicity (4.48) and the limit of `E[−μ(□_m, q)]`, with the duality inequality and the bounds (5.1) for `μ`, and the
partition `𝓠_a` of Definition 3.9 with its minimal scales, are proved in
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/) (the eleven files `GeneralMu*.lean` and
`GeneralMeyersPartition.lean`; namespace `Rigidity.Percolation`, and `Rigidity.Proofs.Cluster.GeneralDim` for the last
file). They continue the section
[The subadditive quantities on the clusters of triadic cubes of Z^d](#the-subadditive-quantities-on-the-clusters-of-triadic-cubes-of-zd)
and
[Section 3 and the isotropy of the homogenized matrix in every dimension](#section-3-and-the-isotropy-of-the-homogenized-matrix-in-every-dimension).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_measure_ne_cappedCube_goodCubes_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD Proposition 4.9 in every dimension `d ≥ 2`: the partition into good cubes differs at some vertex of a triadic cube `A` of scale `m` from the partition capped at the scale `n` with probability at most `C (2·3^{m−n} + 29)^d exp(−c 3ⁿ)`; the second form is for `n` the scale of the cube `V` on which the discrepancy is read. |
| [`Rigidity.Percolation.measurable_cubeMuLoc_localBondSigma`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.indepFun_cubeMuLoc`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.measurable_cubeNu_localBondSigma`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.indepFun_cubeNu`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD (4.39), every `d ≥ 2`: the local version of `−μ(V, q)` is measurable for the bonds inside the local region of `V` (the cube of side `14·3ⁿ + 1` around it), `ν(V, ξ)` for the bonds inside `V`, and the versions on two cubes with disjoint regions are independent (pairs of cubes only). |
| [`Rigidity.Percolation.exists_cubeMuLoc_localization`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD Proposition 4.10 for `μ`, every `d ≥ 2`: the expectations of the local version and of `1{𝒫, V res}(−μ(V, q))` differ by at most `C \|q\|₁² exp(−c 3ⁿ)`, `n` the scale of `V`. For `ν` no localization is needed, because `ν` is local (`measurable_cubeNu_localBondSigma`). |
| [`Rigidity.Percolation.map_cubeMuStat_shift`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean), [`Rigidity.Percolation.exists_cubeMuStat_localization`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean), [`Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_eq`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean) | AD (4.40), every `d ≥ 2`: the law of the stationary local version of `−μ(z + V, q)` does not depend on `z ∈ 3ⁿ ℤ^d`; the same localization error for the stationary version; hence `E[−μ]` is stationary up to `C \|q\|₁² exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_lintegral_sum_cubeMu_subcubes_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveMoments.lean), [`Rigidity.Percolation.sum_cubeMu_subcubes_sub_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveError.lean), [`Rigidity.Percolation.exceptionalEdgeCount_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveError.lean) | AD (4.32) in expectation, every `d ≥ 2`: the error of the subadditivity of `μ` over the subcubes is at most `C \|q\|₁² \|U\| 3^{−n/4}` in expectation, from a deterministic bound by the number of exceptional edges. |
| [`Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean) | AD (4.48), every `d ≥ 2`: for triadic cubes `V`, `U` with the scale `n` of `V` at most that of `U`, `E[−μ(U, q); 𝒫, U res] ≤ E[−μ(V, q); 𝒫, V res] + C \|q\|₁² (3^{−n/4} + exp(−c 3ⁿ))`. |
| [`Rigidity.Percolation.exists_tendsto_cubeMuMean`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_neg_cubeMu_of_scale`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_cubeMuLoc_of_scale`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_cubeMuStat_of_scale`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean) | The limit `lim E[−μ(□_m, q)]` exists, lies between `0` and `C \|q\|₁²`, and is the limit of `E[−μ(V_m, q)]` for every sequence of cubes of scales `m`, and of the expectations of the local and stationary local versions. |
| [`Rigidity.Percolation.cubeMuLimit_smul_add_smul`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuQuadratic.lean), [`Rigidity.Percolation.exists_cubeMuLimit_bounds`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuQuadratic.lean) | The limit of `E[−μ(□_m, q)]` is a quadratic form in `q`, bounded above by `C \|q\|₁²`. |
| [`Rigidity.Percolation.sum_mul_le_neg_cubeMu_add_cubeNu`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean), [`Rigidity.Percolation.sum_mul_le_cubeMuLimit_add_cubeNuLimit`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean) | AD Corollary 4.6 with its face errors, and the duality inequality between the limits, every `d ≥ 2`: `q · ξ ≤ lim E[−μ(□_m, q)] + lim E[ν(□_m, ξ)]`. |
| [`Rigidity.Percolation.exists_cubeMuLimit_two_sided`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean) | The bounds (5.1) for `μ`, every `d ≥ 2`: `c \|q\|² ≤ lim E[−μ(□_m, q)] ≤ C \|q\|₁²`, from the duality inequality and `ā = σ I`. |
| [`Rigidity.Proofs.Cluster.GeneralDim.exists_meyersFailureBound`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean), [`Rigidity.Proofs.Cluster.GeneralDim.exists_measure_stoppingScale_large_le`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean) | AD (3.17) as the failure bound (2.2) for the good cubes of the Meyers estimate, `C₁ exp(−c 3^{ns})` for a cube of scale `n`, and the tail bound of the minimal scales of a local family (Propositions 2.1 and 2.4). |
| [`Rigidity.Proofs.Cluster.GeneralDim.meyersPartition_holds`](PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean) | AD Definition 3.9, every `d ≥ 2` and `p > 𝔭_c(d)`: the partition `𝓠_a` with minimal scales whose tails `P[cells near □_k too large, or Σ size^t > K \|□_k\|] ≤ C exp(−c 3^{kr})` are stretched exponential, for every `t > 0`. |

The forty-three reports for the declarations of this section, which include the supporting declarations named in the
source files, are in [`Audit/Axioms.lean`](Audit/Axioms.lean). Lemma 4.11 and the estimate (4.44) of Proposition 4.10 are not proved: Armstrong and
Dario use them only for (5.31) in the proof of Lemma 5.7, and the planar proof of that lemma replaces them by the local
version of the planar section [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).

Departures from Armstrong and Dario:

- **Localization.** Proposition 4.10 is proved in expectation, and the local version agrees with `μ` exactly off a small
  event (`cubeMuLoc_eq_of_good`). `μ` is localized, as in dimension two, through the partition capped at the scale of `V` on the
  region of side `14·3ⁿ + 1` around `V`, in place of `𝒫_loc^{(n)}(□)` and `𝒞_*^{(n)}(□)`; the error is
  `exp(−c 3ⁿ)`. The exact stationarity (4.40) holds for the stationary local versions `cubeMuStat`; for `E[−μ]` it holds
  up to `C \|q\|₁² exp(−c 3ⁿ)`.
- **Subadditivity error (4.32).** The error in expectation is bounded through the exceptional edges (those that leave
  the subcube or are unresolved), counted at exceptional vertices, with Young's inequality at the parameter
  `3^{−n/4}`; the rate in (4.48) is `3^{−n/4}`, as printed.
- **Definition 3.9.** `meyersGood` asks the Meyers estimate on each child, for every set of the triple closed under its
  open edges and every function harmonic on it, as `rhGood` does for `𝓡`, in place of the estimate `ME_ε(□)` with
  `𝒞_max(3□)`. The printed family has `ME_ε(□_m) ≤ C` where `ME_ε(□) ≤ C` is meant. The minimal scales have the
  stretched exponential tails stated in the table.

## Propositions 5.2 and 5.13, Definition 5.12 and Lemma 5.11 in every dimension, from the bound of Lemma 5.9

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the stochastic forms of Proposition 5.2, Lemma 5.11 and
Proposition 5.13 are proved from the bound of Lemma 5.9, the hypothesis `h59`:
`D_n ≤ C₉ σ₉ⁿ + C₉ Σ_{l ≤ n} ρ₉^{n−l} τ_l` for `n ≥ N₉`, with `σ₉, ρ₉ ∈ [0, 1)`, the same hypothesis
as for Lemma 5.10 in every dimension. The modules are the thirteen files `GeneralBoundN`,
`GeneralFieldPairing`, `GeneralFlatnessNuExpect`, `GeneralOmegaSupRate`, `GeneralRhoLocal`,
`GeneralRhoSubadditive`, `GeneralSIStepTwo`, `GeneralSIUpgrade`, `GeneralSIUpgradeOs`,
`GeneralSubaddOs`, `GeneralSubaddRates`, `GeneralSubaddTail` and `GeneralSubaddTailMain` of
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/)
(namespace `Rigidity.Percolation`).

| Lean declaration | Statement |
| --- | --- |
| `exists_cubeRho_majorant_of_decay` | AD (5.42), given `h59`: the quantity `ρ(V) = sup_q \|q\|⁻² ω₊(V, q)` has an almost surely integrable majorant with expectation at most `C rⁿ`. |
| `exists_cubeRho_tail_of_decay` | AD Lemma 5.11, tail form, given `h59`: the tail of `ρ(□_{n+3+j})` off the event that the partition cubes have scale at most `l`. |
| `exists_cubeSubaddGood_tail_of_decay` | AD Proposition 5.2, tail form, given `h59`: the event that `\|μ(□_m, q) + (1/2) q · ā⁻¹ q\|` and `\|ν(□_m, ā⁻¹ q) − (1/2) q · ā⁻¹ q\|` are at most `K \|q\|² λᵐ` fails with probability at most `K' exp(−c (3ᵐ)ˢ)`. |
| `exists_cubeBoundN_of_decay` | AD Definition 5.12 and Proposition 5.13, given `h59`: a random scale `N ≤ O_r(θ)` above which the bounds of Proposition 5.2 hold at the mesoscopic scales `n(m) ≤ m ≤ L n(m)`. |
| `exists_cubeSubaddErr_isOsBond_of_decay` | AD Proposition 5.2, (5.2) and (5.3), given `h59`: for every triadic cube `V` the random error `X(V)` of `μ(V, q) + (1/2) q · ā⁻¹ q` and `ν(V, ā⁻¹ q) − (1/2) q · ā⁻¹ q` is measurable and `X(V) ≤ O_r(C 3^{−α scale V})` with `r = 1/(2d − 1)`. |
| `exists_cubeOmega_isOsBond_of_decay` | AD Lemma 5.11, given `h59`: `sup_q \|q\|⁻² \|ω(V, q)\| ≤ O_r(C 3^{−α scale V})` with `r = 1/(2d − 1)` and a measurable majorant, which also bounds `ρ(V)`. |
| `exists_neg_cubeMu_le_isOsBond_of_decay` | AD (4.17), given `h59`: `−μ(V, q) ≤ (K + Z(V)) \|q\|²` with `Z(V) ≤ O_r(C 3^{−α scale V})`, `r = 1/(2d − 1)`. |

Departures from Armstrong and Dario:

- **Hypothesis.** The three results are proved from the bound of Lemma 5.9 (`h59`), which is not proved in every
  dimension; in `d = 2` it is proved (`exists_planarOmegaD_decay_holds`).
- **Order.** AD prove Lemma 5.11 first and derive Proposition 5.2 from it; here, as in `d = 2`, both come from the
  tail bounds of `GeneralSubaddTailMain.lean`, and Lemma 5.11 is the difference of the two error forms of
  Proposition 5.2.
- **Exponents.** The exponent of the `O_s` bounds is `1/(2d − 1)`, which depends only on `d`, as the `s(d)` of AD.
  For (4.17) AD print `O_{1/(2d+1)}(C |q|² size(□)⁻¹)` with no hypothesis; the Lean bound has the rate
  `size(□)^{−α}` of Proposition 5.2 in place of `size(□)⁻¹`, and the exponent `1/(2d − 1) ≥ 1/(2d + 1)`.
- **`ν` at `ā⁻¹ q`.** `ν` is evaluated at the slopes `ā⁻¹ q`; this is equivalent to AD's statement for every slope,
  since `ā = σ I` with `σ > 0` (`exists_cubeAhom_eq_smul_one`).
- **Rates.** The rate of (5.42) is `C rⁿ` for some `r < 1` (AD: `C 3^{−nα}`); Lemma 5.11 in tail form is stated on
  the event that the partition cubes have scale at most `l`, with a constant `C₁(l)` (AD: the constant through the
  minimal scales).


## Lemma 5.7 in every dimension

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, display (5.25) of Lemma 5.7 holds for every triadic cube `V`
of scale `n` and every slope `q`:
`E[Σ_j (|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_𝒫⟩_V − (ā_{□_n}⁻¹ q)_j)²] ≤ C |q|² (τ_n + 3^{−n/4})`. The modules are
`GeneralSolenoidalField`, `GeneralSubcubeCrossing`, `GeneralRestrictField`, `GeneralOneVarEst`,
`GeneralSwitchLocLocal`, `GeneralSwitchLocCompare`, `GeneralSwitchLocProb`, `GeneralWeakConvOrigin` and
`GeneralWeakConvHolds` of
[`PercolationClusterHomogenization/Proofs/Cluster/`](PercolationClusterHomogenization/Proofs/Cluster/)
(namespace `Rigidity.Percolation`).

| Lean declaration | Statement |
| --- | --- |
| `cubeSolenoidalField`, `latticeEdgePairing_cubeSolenoidalField_eq_zero`, `latticeEdgePairing_cubeSolenoidalField_origin` | AD Lemma 5.7, Step 1, and (5.28) with right side zero: for a coordinate direction `e_k` and `l ≠ k`, the plane curl of `z_l χ_n(z)` in the coordinates `k, l` is exactly divergence free, bounded by `10`, equal to `e_k` on the edges of `□_n` and zero off the edges of `□_{n+1}`; its pairing with every gradient over `□_{n+1}` vanishes. |
| `exists_lintegral_coarse_cubeMuMinimizer_le` | AD (4.24) in expectation: `E[Σ_V \|∇[u(·, V, q)]_𝒫\|²] ≤ C \|q\|² \|V\|^{1+1/a}` for every `a ≥ 1`. |
| `latticeEdgePairing_sub_sum_subcubesAt_sq_le`, `exists_lintegral_latticeEdgePairing_sub_sum_subcubesAt_le` | AD Lemma 5.7, Step 2, (5.29): the pairing of a bounded field over `U` minus the sum over the subcubes is the pairing over the edges between subcubes, at most `d \|U\|/3ⁿ` of them. |
| `exists_lintegral_cubeMuRestrictFieldError_le` | AD Lemma 5.5 for the pairings with a field `g`, `\|g\| ≤ G`, as used in Step 3 of the proof of Lemma 5.7: the bound of (5.12) with the factor `G²`. |
| `exists_lintegral_sum_subcube_cubeSolenoidal_sq_le` | AD (5.30): `E[\|Σ_V \|□_n\|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V\|²] ≤ C \|q\|² (τ_n + 3^{−n/4})` for the solenoidal field `g` and the subcubes `V` of scale `n` of `□_{n+1}`, `n ≥ 2d`. |
| `cubeSwitchLoc`, `indepFun_cubeSwitchLoc`, `exists_lintegral_sq_sub_cubeSwitchLoc_le` | AD (5.31): local versions of the subcube pairings, measurable for the bonds inside the subcube and so independent across disjoint subcubes, close in mean square, `C G² \|q\|₁² 3^{−n/4}`, for `n ≥ 8d`. |
| `exists_variance_cubeMuGradAvg_origin_le`, `exists_lintegral_cubeMuGradAvg_origin_le` | AD Lemma 5.7 for `□_n`, `n ≥ 8d`: the variance bound and (5.25). |
| `cubeMuGradAvg_shift_eq_of_good`, `exists_lintegral_cubeMuGradAvg_sub_le` | AD Lemma 5.7, (5.25), for every triadic cube, by translation from `□_n`. |

Departures from Armstrong and Dario:

- **Step 1.** AD take a smooth divergence-free continuum field from the proof of Lemma 3.2 of Armstrong and
  Smart and discretize it, with an error `C 3^{−n}` in (5.28). The Lean field is an exactly divergence-free
  lattice field: the field `G_i = Σ_j D_j^− A_{ij}` of the antisymmetric potential with `A_{kl} = −A_{lk} = z_l χ_n(z)`
  and the other entries zero. It vanishes on the edges not inside `□_{n+1}` (AD's printed support
  `[−3, 3]^d`, rescaled, does not lie inside `□_{n+1}`, whose faces are at `3/2`), so the right side of (5.28) is `0`.
- **Lemma 5.5 with a field.** The restriction step at the line `⟨∇ f_U, g⟩` of AD is proved by the proof of
  Lemma 5.5 itself, with the pairing with `g` in place of the pairings with the directions `e_i`, which gives
  the factor `G²` in place of `d`.
- **Localization.** AD localize with Lemma 4.11. Here the subcube pairing is compared with a local version
  built from the partition capped at the scale `⌊n/(8d)⌋` and the field and the slope restricted to the inner
  cube at distance `3^{k+2}`, by the second variation and Lemma 3.3; the local version depends only on the bonds
  inside the subcube on the event that the partition agrees with the capped partition, whose complement has
  probability at most `C (2·3^{n−k} + 29)^d exp(−c 3^k)`.
- **Small scales.** For `n < 8d` the bound follows from the deterministic bound
  `\|V\|⁻¹ \|⟨∇[u]_𝒫, e_j⟩_V\| ≤ 2d K² 3^{(2d−1)n} \|q\|₁`.
