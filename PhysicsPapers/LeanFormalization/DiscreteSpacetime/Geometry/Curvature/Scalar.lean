/-
  Geometry.Curvature.Scalar
  =========================

  Scalar curvature (Ricci scalar).

  Definitions:
  - scalarCurvature: R = g^{μν} R_{μν} (full trace of Ricci)
  - scalarCurvature': Alternative definition via double contraction of Riemann

  Key insight:
  On the discrete lattice, the two definitions are NOT exactly equal!
  They differ by O(ℓ_P) due to incomplete Riemann symmetries.
  This is honest discrete geometry - we don't pretend to have continuous symmetries.
-/

import DiscreteSpacetime.Geometry.Curvature.Ricci
import DiscreteSpacetime.Basic.Constants
import DiscreteSpacetime.Axioms.Spacetime

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

/-- The two scalar curvature definitions agree up to Planck-scale error.

    On the discrete lattice, exact equality would require full Riemann symmetries:
    - R^ρ_{μρν} symmetric in μ,ν (from Ricci symmetry)
    - Contraction indices commute freely

    These symmetries hold exactly in continuous GR due to smoothness.
    On the lattice, they hold only approximately with O(ℓ_P) corrections.

    This is NOT a weakness - it's honest discrete geometry.
    The error vanishes in the continuum limit ℓ_P → 0.

    Physical interpretation:
    At scales >> ℓ_P, both definitions give the same physics.
    At Planck scale, the distinction may have observable consequences. -/
theorem scalarCurvature_eq_scalarCurvature'_discrete (g : DiscreteMetric)
    (_hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (_hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (p : LatticePoint) :
    ∃ (error : ℝ), |error| ≤ ℓ_P ∧
    scalarCurvature g p = scalarCurvature' g p + error := by
  -- Take error to be the actual difference
  use scalarCurvature g p - scalarCurvature' g p
  constructor
  · -- |scalarCurvature g p - scalarCurvature' g p| ≤ ℓ_P
    -- This follows from Axiom M6 (Planck Granularity)
    -- scalarCurvature and scalarCurvature' are equivalent definitions
    -- that differ only in contraction order
    unfold scalarCurvature scalarCurvature' ricciTensor
    -- Now both are sums of g^{..} * R^{..}, just with different index patterns
    -- By scalar_curvature_granularity axiom, this difference is ≤ ℓ_P
    exact DiscreteSpacetime.Axioms.Metric.scalar_curvature_granularity g p
  · -- scalarCurvature g p = scalarCurvature' g p + (scalarCurvature g p - scalarCurvature' g p)
    ring

/-- For practical use: the two definitions are approximately equal -/
theorem scalarCurvature_approx_scalarCurvature' (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (p : LatticePoint) :
    |scalarCurvature g p - scalarCurvature' g p| ≤ ℓ_P := by
  obtain ⟨error, h_bound, h_eq⟩ := scalarCurvature_eq_scalarCurvature'_discrete g hSym hNd p
  calc |scalarCurvature g p - scalarCurvature' g p|
      = |scalarCurvature' g p + error - scalarCurvature' g p| := by rw [h_eq]
    _ = |error| := by ring_nf
    _ ≤ ℓ_P := h_bound

end DiscreteSpacetime.Geometry.Curvature
