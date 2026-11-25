import Mathlib
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds
import HomogenizationAudit.OrderZero.SolutionBasic

/-!
# Solution: `OrderZero` (Theorem 2 (iii) of Armstrong and Dario at order zero)

The challenge module `HomogenizationAudit/OrderZero/Challenge.lean` imports only Mathlib and states
`armstrong_dario_order_zero` with one intentional `sorry`. This solution imports the library together
with `HomogenizationAudit.OrderZero.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the statement from `Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`
(`PercolationClusterHomogenization/Proofs/Regularity/GeneralOrderZeroHolds.lean`).

The transport is definitional: the audit vocabulary is a token-for-token copy of the
Lattice-Probability definitions that `LatticeProb.External.ArmstrongDarioOrderZero` unfolds to, as in
`RigidityAudit/Lipschitz/Bridge.lean` of Percolation-Rigidity, where the two propositions are equal by
`rfl`.
-/

namespace PercolationClusterHomogenization
namespace StatementAudit
namespace OrderZero

/-- **Theorem 2 (iii) at `k = 0`** of Armstrong and Dario, for Bernoulli bond percolation with
zero-one conductances. -/
theorem armstrong_dario_order_zero : ArmstrongDarioOrderZero :=
  Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds

end OrderZero
end StatementAudit
end PercolationClusterHomogenization
