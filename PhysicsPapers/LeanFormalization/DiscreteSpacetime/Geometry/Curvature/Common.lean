/-
  Geometry.Curvature.Common
  =========================

  Core definitions for curvature tensors on the discrete Planck lattice.

  This module defines:
  - christoffelDerivative: Partial derivative of Christoffel symbols
  - riemannTensor: Riemann curvature tensor R^ρ_{σμν}
  - riemannLower: Fully covariant Riemann tensor R_{ρσμν}
  - christoffelDerivative_lower_symm: Symmetry lemma for derivatives

  All other curvature modules import this one.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import DiscreteSpacetime.Basic.Lattice
import DiscreteSpacetime.Basic.Operators
import DiscreteSpacetime.Geometry.Metric
import DiscreteSpacetime.Geometry.Connection

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open Matrix
open BigOperators
open Finset

/-! ## Christoffel Derivative -/

/-- Partial derivative of Christoffel symbol along direction α.
    Uses symmetric difference for second-order accuracy. -/
noncomputable def christoffelDerivative (g : DiscreteMetric) (ρ μ ν α : Fin 4)
    (p : LatticePoint) : ℝ :=
  symmetricDiff (fun q => christoffelSymbol g ρ μ ν q) α p

/-! ## Riemann Curvature Tensor -/

/-- Riemann curvature tensor R^ρ_{σμν}.
    Definition:
    R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}

    This measures the non-commutativity of covariant derivatives:
    [∇_μ, ∇_ν] V^ρ = R^ρ_{σμν} V^σ -/
noncomputable def riemannTensor (g : DiscreteMetric) (ρ σ μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  -- First two terms: partial derivatives of Christoffel symbols
  christoffelDerivative g ρ ν σ μ p - christoffelDerivative g ρ μ σ ν p +
  -- Last two terms: products of Christoffel symbols (Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ})
  ∑ lam : Fin 4, christoffelSymbol g ρ μ lam p * christoffelSymbol g lam ν σ p -
  ∑ lam : Fin 4, christoffelSymbol g ρ ν lam p * christoffelSymbol g lam μ σ p

/-- Notation for Riemann tensor -/
notation "R[" ρ "," σ "," μ "," ν "]" => riemannTensor · ρ σ μ ν

/-! ## Lowered Riemann Tensor -/

/-- Lower the first index to get fully covariant Riemann tensor.
    R_{ρσμν} = g_{ρλ} R^λ_{σμν} -/
noncomputable def riemannLower (g : DiscreteMetric) (ρ σ μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  ∑ lam : Fin 4, (g p) ρ lam * riemannTensor g lam σ μ ν p

/-! ## Christoffel Derivative Symmetry -/

/-- Christoffel derivative is symmetric in the second and third indices.
    This is inherited from christoffel_symmetry.

    ∂_α Γ^ρ_{μν} = ∂_α Γ^ρ_{νμ}

    This follows because Γ^ρ_{μν} = Γ^ρ_{νμ} at every point. -/
theorem christoffelDerivative_lower_symm (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ μ ν α : Fin 4) (p : LatticePoint) :
    christoffelDerivative g ρ μ ν α p = christoffelDerivative g ρ ν μ α p := by
  unfold christoffelDerivative symmetricDiff
  -- At both shifted points, use christoffel_symmetry
  have hpos : christoffelSymbol g ρ μ ν (p.shiftPos α) = christoffelSymbol g ρ ν μ (p.shiftPos α) :=
    christoffel_symmetry g hSym ρ μ ν (p.shiftPos α)
  have hneg : christoffelSymbol g ρ μ ν (p.shiftNeg α) = christoffelSymbol g ρ ν μ (p.shiftNeg α) :=
    christoffel_symmetry g hSym ρ μ ν (p.shiftNeg α)
  simp only [hpos, hneg]

end DiscreteSpacetime.Geometry.Curvature
