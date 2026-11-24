import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.KestenCrossing

/-!
# The crossings of an annulus

`AnnulusCrossings ω R`: the long crossings of the four rectangles of the annulus `Q_{2R} \ Q_R`;
and the statement `CrossingProbabilityStep` that an exponential crossing estimate for long
rectangles gives an exponential bound on the failure of these crossings.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.External

/-- The crossings at scale `R`: the long crossings of the bottom `[-2R, 2R] × [-2R, -R-1]`, the
top `[-2R, 2R] × [R+1, 2R]`, the left `[-2R, -R-1] × [-2R, 2R]` and the right
`[R+1, 2R] × [-2R, 2R]` rectangles of the annulus `Q_{2R} \ Q_R`, and the radial crossing of
`[R+1, 4R] × [0, R]` joining the right rectangles at scales `R` and `2R`. -/
def AnnulusCrossings (ω : Configuration 2) (R : ℕ) : Prop :=
  HasOpenCrossing ω ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 0 ∧
  HasOpenCrossing ω ![-(2 * R : ℤ), R + 1] (4 * R) (R - 1) 0 ∧
  HasOpenCrossing ω ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 1 ∧
  HasOpenCrossing ω ![(R : ℤ) + 1, -(2 * R)] (4 * R) (R - 1) 1 ∧
  HasOpenCrossing ω ![(R : ℤ) + 1, 0] (3 * R - 1) R 0

/-- Step `step:5.14-union-bound`: an exponential crossing estimate for long rectangles gives an
exponential bound on the probability that one of the crossings at scale `R` fails. -/
def CrossingProbabilityStep : Prop :=
  ∀ (p : unitInterval) (C c : ℝ), 0 < C → 0 < c →
    (∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n)))) →
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ R : ℕ,
      latticeBondLaw 2 p {ω | ¬ AnnulusCrossings ω R} ≤
        ENNReal.ofReal (C' * (R + 1) * Real.exp (-(c' * R)))

end Rigidity.Steps.Section5
