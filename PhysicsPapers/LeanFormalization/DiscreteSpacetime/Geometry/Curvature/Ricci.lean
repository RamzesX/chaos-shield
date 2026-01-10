/-
  Geometry.Curvature.Ricci
  ========================

  Ricci tensor and its properties.

  Definitions:
  - ricciTensor: R_{μν} = R^ρ_{μρν} (trace of Riemann)
  - ricciTensor': Alternative definition via metric contraction

  TODO (MODERATE):
  - ricci_symmetric: R_{μν} = R_{νμ} (depends on riemann_lower_pair_swap)
-/

import DiscreteSpacetime.Geometry.Curvature.Common

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open Matrix
open BigOperators
open Finset

/-! ## Ricci Tensor Definitions -/

/-- Ricci tensor R_{μν} = R^ρ_{μρν} (contraction on first and third indices).
    This is the trace of the Riemann tensor. -/
noncomputable def ricciTensor (g : DiscreteMetric) (μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  ∑ ρ : Fin 4, riemannTensor g ρ μ ρ ν p

/-- Alternative: Contract using the metric.
    R_{μν} = g^{ρσ} R_{ρμσν} -/
noncomputable def ricciTensor' (g : DiscreteMetric) (μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, (inverseMetric (g p)) ρ σ * riemannLower g ρ μ σ ν p

/-! ## Ricci Tensor Symmetry -/

/-- Ricci tensor is symmetric: R_{μν} = R_{νμ}

    PROOF STRATEGY:
    This follows from riemann_lower_pair_swap (from Symmetries.lean):
    R_{ρμρν} = R_{ρνρμ} by pair swap symmetry

    Since ricciTensor is a sum over ρ, the symmetry in μ,ν follows
    from the symmetry of each term. -/
theorem ricci_symmetric (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (μ ν : Fin 4) (p : LatticePoint) :
    ricciTensor g μ ν p = ricciTensor g ν μ p := by
  unfold ricciTensor
  -- Use pair swap symmetry of Riemann tensor
  sorry -- Follows from riemann_lower_pair_swap

end DiscreteSpacetime.Geometry.Curvature
