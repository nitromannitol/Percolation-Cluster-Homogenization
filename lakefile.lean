import Lake
open Lake DSL

package «percolation-cluster-homogenization» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @
    "7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069"

/-- The formalization: every module under `PercolationClusterHomogenization/`. A warning is an
error. -/
@[default_target]
lean_lib PercolationClusterHomogenization where
  globs := #[.andSubmodules `PercolationClusterHomogenization]
  leanOptions := #[⟨`warningAsError, true⟩]

/-- The comparator pairs `HomogenizationAudit/*/Challenge.lean`, `HomogenizationAudit/*/Solution.lean`.
Not a default target: it builds only on demand (`lake build HomogenizationAudit`), so the ordinary
build is unchanged; each challenge elaborates with its one intentional `sorry`. -/
lean_lib HomogenizationAudit where
  globs := #[.submodules `HomogenizationAudit]
