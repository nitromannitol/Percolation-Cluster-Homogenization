import LatticeProb.Prob.Percolation.LSSThinInstantiation
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing
import LatticeProb.Prob.Strassen.Defs
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.KestenCrossing
import PercolationClusterHomogenization.External.WellConnected

/-!
# Proposition 5.21: the steps of the disjoint paths to infinity

Proposition 5.21 (`prop:disjoint-paths-to-infinty-exponential`, corrected draft L2154-2158, proof
L2253-2276) bounds the probability of the complement of the event `E_R(x)`
(`Rigidity.Section5.eventE`). The proof runs through the renormalized percolation process of size
`R` (`renormField R`, the site `z` open when `(2R + 1) z + Q_{11R/10}` is very good) and splits into
a probabilistic and a deterministic half.

**Probabilistic half.** `RenormClusterBound p`: a site of the renormalized lattice misses the
infinite open clusters of the renormalized process of size `R` with probability at most
`C exp(-c R^s)`. Two routes are given.

* The printed route (`renormClusterBound_of_domination`): Lemma 5.23
  (`RenormalizedDominationStmt`) and
  * `InfiniteClusterMeasurableStep`: the event that a site lies in an infinite open cluster is
    measurable (it is increasing: `isIncreasingSet_inInfiniteSiteCluster`), so the domination
    applies to it;
  * `SiteDensityNearOneStep` (`step:5.21-site-density`; the printed proof cites
    Grimmett, *Percolation*, Theorem 8.92): for Bernoulli site percolation of parameter `q` on
    `ℤ²`, `1 - θ_site(q) ≤ C (1 - q)`. A Peierls bound gives it: if the open cluster of the origin
    is finite, a closed `*`-circuit surrounds the origin, and the `*`-circuits of length `n`
    surrounding it number at most `n 8^n`.
* The route without Liggett-Schonmann-Stacey (`renormClusterBound_of_peierls`), from Proposition
  2.3 (`WellConnectedInput`), Kesten's crossing estimate (`KestenRectangleCrossing`),
  `p_c(2) < p`, the steps `VeryGoodProbabilityStep`, `RenormFieldMeasurableStep`,
  `RenormFieldOneDependentStep` of Lemma 5.23, and
  * `OneDependentPeierlsStep`: a `1`-dependent field on `ℤ²` (for the `ℓ^∞` distance) whose sites
    are closed with probability at most `ε` leaves a site outside its infinite open clusters with
    probability at most `C₀ ε^a`. A closed `*`-circuit of length `n` has at least `n / 9` sites
    at pairwise `ℓ^∞` distance at least `2`, all closed with probability at most `ε^{n/9}`.

  Proposition 5.21 needs no more of Lemma 5.23 than this Peierls bound: the stochastic domination
  (Liggett-Schonmann-Stacey, Theorem 1.3) is used in the printed proof only to transfer
  `1 - θ_site(q) ≤ C (1 - q)` to the renormalized process.

**Deterministic half** (`step:5.21-renorm-paths`, eq. `implication-renormalized-cluster`):
`RenormalizedClusterPathsStep`, if the renormalized site `z` lies in an infinite open cluster
and `x ∈ (2R + 1) z + Q_R`, then `E_R(x)` holds, for `R ≥ R₁(C_f)`. It follows
(`renormalizedClusterPaths_of_cut`) from
* `MengerRaysStep` (Menger's theorem for rays, no literature input): in an open cluster, if no
  set of fewer than `k` vertices meets every infinite path starting in the finite set `S`, there
  are `k` disjoint infinite paths starting in `S`. Finite Menger in the ball of radius `n` around
  `S`, with the sphere of radius `n` as target, gives `k` disjoint paths from `S` to that sphere
  for each `n`; truncation at the first visit of a smaller sphere and König's lemma give rays.
* `KestenChannelCutStep` (the cut form of `step:5.21-renorm-paths`): removing at most `C_f`
  vertices of `𝒞_∞` leaves an infinite path of `𝒞_∞` starting in `S` and avoiding them. The
  Kesten channels of one direction of a very good cube are disjoint, so at most `C_f` of them are
  hit. A path of `S` from `x` to the first exit from `x + Q_{⌊R/10⌋}` stays in
  `(2R + 1) z + Q_{⌊11R/10⌋}` and crosses about `√R / 10` channels transversally, each of which
  it meets (a left-right and a top-bottom crossing of a lattice rectangle share a vertex). Along
  an infinite path of open renormalized sites from `z`, an unhit horizontal and an unhit vertical
  channel of one cube meet; the overlap of two neighbouring cubes, of width at least
  `2 ⌊R/10⌋`, contains about `√R / 5` transverse channels of the first cube, one unhit, and it
  meets the unhit parallel channels of both cubes. The unhit channels along the path thus form an
  infinite connected open set avoiding the removed vertices, containing a vertex of `S`.

The printed proof builds the `C_f + 1` disjoint paths directly by gluing matching channels of
consecutive cubes along a path to infinity of the renormalized cluster (L2260-2263). It does not
address cubes of non-consecutive sites of that path which overlap (diagonal neighbours, or
returns of the path next to itself), where the glued paths of different channels may meet. The
cut form above with Menger's theorem avoids this; the inclusion `implication-renormalized-cluster`
and Proposition 5.21 are unchanged.

The well-connectedness of the very good cubes is not used by the deterministic half: planar
crossings of the channels suffice.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The open subgraph of a site configuration `η` of the renormalized lattice `ℤ²`: two nearest
neighbours are adjacent when both are open. -/
def siteOpenGraph (η : PlanarCarrier → Bool) : SimpleGraph PlanarCarrier where
  Adj z w := |z.1 - w.1| + |z.2 - w.2| = 1 ∧ η z = true ∧ η w = true
  symm := ⟨fun z w h => ⟨by rw [abs_sub_comm w.1, abs_sub_comm w.2]; exact h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun z h => by simp at h⟩

/-- The site `z` of the renormalized lattice lies in an infinite open cluster of `η`. -/
def InInfiniteSiteCluster (η : PlanarCarrier → Bool) (z : PlanarCarrier) : Prop :=
  η z = true ∧ {w | (siteOpenGraph η).Reachable z w}.Infinite

/-- Step `step:5.21-cluster-measurable`: the event that a site lies in an infinite open cluster
is measurable. -/
def InfiniteClusterMeasurableStep : Prop :=
  ∀ z : PlanarCarrier, MeasurableSet {η : PlanarCarrier → Bool | InInfiniteSiteCluster η z}

end Rigidity.Steps.Section5
