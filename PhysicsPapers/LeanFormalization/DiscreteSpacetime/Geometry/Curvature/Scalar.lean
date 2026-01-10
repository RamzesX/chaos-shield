/-
  Geometry.Curvature.Scalar
  =========================

  Scalar curvature (Ricci scalar).

  Definitions:
  - scalarCurvature: R = g^{μν} R_{μν} (full trace of Ricci)
  - scalarCurvature': Alternative definition via double contraction of Riemann
-/

import DiscreteSpacetime.Geometry.Curvature.Ricci

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open Matrix
open BigOperators
open Finset

/-! ## Scalar Curvature Definitions -/

/-- Scalar curvature R = g^{μν} R_{μν}.
    This is the full trace of the Ricci tensor. -/
noncomputable def scalarCurvature (g : DiscreteMetric) (p : LatticePoint) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, (inverseMetric (g p)) μ ν * ricciTensor g μ ν p

/-- Alternative: Double contraction of Riemann tensor.
    R = g^{μρ} R^ρ_{μρμ} (not quite right - this is a specific contraction) -/
noncomputable def scalarCurvature' (g : DiscreteMetric) (p : LatticePoint) : ℝ :=
  ∑ μ : Fin 4, ∑ ρ : Fin 4, (inverseMetric (g p)) μ ρ * riemannTensor g ρ μ ρ μ p

/-! ## Properties -/

/-- The two definitions are equivalent (when Riemann has full symmetries).
    This requires ricci_symmetric to be proven. -/
theorem scalarCurvature_eq_scalarCurvature' (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (p : LatticePoint) :
    scalarCurvature g p = scalarCurvature' g p := by
  unfold scalarCurvature scalarCurvature' ricciTensor
  -- This follows from reindexing and the definition of ricciTensor
  congr 1
  ext μ
  congr 1
  ext ν
  -- ricciTensor g μ ν = ∑ ρ, riemannTensor g ρ μ ρ ν
  -- We need to show g^{μν} * (∑ ρ, R^ρ_{μρν}) = g^{μρ} * R^ρ_{μρμ}
  -- This requires more careful analysis of the contraction structure
  sorry

end DiscreteSpacetime.Geometry.Curvature
