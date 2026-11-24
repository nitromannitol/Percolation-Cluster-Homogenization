/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import PercolationClusterHomogenization.Vendor.LHCH.Model.Lattice
import PercolationClusterHomogenization.Vendor.LHCH.Model.Symmetry
import PercolationClusterHomogenization.Vendor.LHCH.Model.Conductance
import PercolationClusterHomogenization.Vendor.LHCH.Model.Coarse
import PercolationClusterHomogenization.Vendor.LHCH.Model.Corrector
import PercolationClusterHomogenization.Vendor.LHCH.Model.Continuum
import PercolationClusterHomogenization.Vendor.LHCH.Model.Hypotheses
import PercolationClusterHomogenization.Vendor.LHCH.Model.CoarseMoments
