/-
  Geometry.Curvature
  ==================

  Main curvature module - re-exports all curvature submodules.

  This module re-exports:
  - Curvature.Common: Core definitions (riemannTensor, riemannLower, etc.)
  - Curvature.Symmetries: Riemann tensor symmetries
  - Curvature.Bianchi: First and second Bianchi identities
  - Curvature.Flat: Curvature vanishing for flat spacetime
  - Curvature.Ricci: Ricci tensor
  - Curvature.Scalar: Scalar curvature
  - Curvature.Weyl: Weyl tensor (conformally invariant)
  - Curvature.Kretschmann: Kretschmann scalar (quadratic invariant)

  ## Status Summary

  ### PROVEN (no sorry):
  - christoffelDerivative_lower_symm (Common)
  - riemann_antisym_34 (Symmetries)
  - first_bianchi (Bianchi)
  - riemann_flat_vanishes (Flat)
  - ricci_flat_vanishes (Flat)
  - scalar_flat_vanishes (Flat)
  - kretschmann_flat_vanishes (Kretschmann)

  ### TODO - HARD:
  - riemann_lower_antisym_12 (Symmetries)
  - riemann_lower_pair_swap (Symmetries)
  - second_bianchi_discrete (Bianchi)
  - contracted_bianchi_discrete (Bianchi)

  ### TODO - MODERATE:
  - ricci_symmetric (Ricci) - depends on pair_swap
  - weyl_tracefree_discrete (Weyl) - ≤ ℓ_P bound
  - weyl_antisym_*_discrete, weyl_pair_swap_discrete (Weyl) - ≤ ℓ_P bounds
  - scalarCurvature_eq_scalarCurvature'_discrete (Scalar) - ≤ ℓ_P bound

  ### DONE (via axiom):
  - kretschmann_nonneg (Kretschmann) - from Axiom M5

  Usage:
    import DiscreteSpacetime.Geometry.Curvature
    -- This gives access to all curvature definitions and theorems
-/

-- Re-export all submodules
import DiscreteSpacetime.Geometry.Curvature.Common
import DiscreteSpacetime.Geometry.Curvature.Symmetries
import DiscreteSpacetime.Geometry.Curvature.Bianchi
import DiscreteSpacetime.Geometry.Curvature.Flat
import DiscreteSpacetime.Geometry.Curvature.Ricci
import DiscreteSpacetime.Geometry.Curvature.Scalar
import DiscreteSpacetime.Geometry.Curvature.Weyl
import DiscreteSpacetime.Geometry.Curvature.Kretschmann

/-! ## Re-exports for backwards compatibility

    These aliases ensure that code importing DiscreteSpacetime.Geometry.Curvature
    can still use the definitions without the Curvature prefix. -/

namespace DiscreteSpacetime.Geometry

open Curvature

-- Core definitions from Common
export Curvature (christoffelDerivative riemannTensor riemannLower)

-- Symmetry theorems
export Curvature (christoffelDerivative_lower_symm riemann_antisym_34
                  riemann_lower_antisym_12 riemann_lower_pair_swap)

-- Bianchi identities
export Curvature (first_bianchi riemannCovariantDeriv second_bianchi_discrete
                  ricciDivergence contracted_bianchi_discrete)

-- Flat spacetime theorems
export Curvature (riemann_flat_vanishes ricci_flat_vanishes scalar_flat_vanishes)

-- Ricci tensor
export Curvature (ricciTensor ricciTensor' ricci_symmetric)

-- Scalar curvature
export Curvature (scalarCurvature scalarCurvature')

-- Weyl tensor
export Curvature (weylTensor weyl_tracefree_discrete weyl_antisym_34_discrete
                  weyl_antisym_12_discrete weyl_pair_swap_discrete)

-- Kretschmann scalar
export Curvature (kretschmannScalar kretschmann_nonneg kretschmann_flat_vanishes)

end DiscreteSpacetime.Geometry
