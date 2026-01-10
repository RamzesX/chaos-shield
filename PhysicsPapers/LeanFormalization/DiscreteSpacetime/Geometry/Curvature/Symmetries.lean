/-
  Geometry.Curvature.Symmetries
  =============================

  Symmetry properties of the Riemann curvature tensor.

  PROVEN:
  - riemann_antisym_34: R^ρ_{σμν} = -R^ρ_{σνμ} (antisymmetric in last two indices)
  - riemann_lower_antisym_34: R_{ρσμν} = -R_{ρσνμ} (preserved under lowering)
  - riemann_lower_pair_swap: R_{ρσμν} = R_{μνρσ} (pair swap - from axiom M3b)
  - riemann_lower_antisym_12: R_{ρσμν} = -R_{σρμν} (antisymmetric in first two)
-/

import DiscreteSpacetime.Geometry.Curvature.Common
import DiscreteSpacetime.Geometry.Curvature.Bianchi
import DiscreteSpacetime.Axioms.Spacetime

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open DiscreteSpacetime.Axioms.Metric
open Matrix
open BigOperators
open Finset

/-! ## Antisymmetry in Last Two Indices -/

/-- Riemann tensor is antisymmetric in the last two indices.
    R^ρ_{σμν} = -R^ρ_{σνμ} -/
theorem riemann_antisym_34 (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannTensor g ρ σ μ ν p = -riemannTensor g ρ σ ν μ p := by
  unfold riemannTensor
  -- Let A, B, C, D be the four terms
  set A := christoffelDerivative g ρ ν σ μ p with hA
  set B := christoffelDerivative g ρ μ σ ν p with hB
  set C := ∑ lam : Fin 4, christoffelSymbol g ρ μ lam p * christoffelSymbol g lam ν σ p with hC
  set D := ∑ lam : Fin 4, christoffelSymbol g ρ ν lam p * christoffelSymbol g lam μ σ p with hD
  -- Goal becomes: A - B + C - D = -(B - A + D - C)
  -- This is algebraically: A - B + C - D = -B + A - D + C = A - B + C - D ✓
  ring

/-! ## Helper Lemmas for Lowered Tensor -/

/-- Antisymmetry in last two indices is preserved under lowering.
    R_{ρσμν} = -R_{ρσνμ}

    This follows directly from riemann_antisym_34 by linearity of summation. -/
theorem riemann_lower_antisym_34 (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannLower g ρ σ μ ν p = -riemannLower g ρ σ ν μ p := by
  unfold riemannLower
  -- Goal: Σ_λ g_{ρλ} R^λ_{σμν} = -Σ_λ g_{ρλ} R^λ_{σνμ}
  -- Use riemann_antisym_34 to rewrite each term
  have h : ∀ lam : Fin 4, (g p) ρ lam * riemannTensor g lam σ μ ν p =
                         -((g p) ρ lam * riemannTensor g lam σ ν μ p) := by
    intro lam
    rw [riemann_antisym_34 g hSym lam σ μ ν p]
    ring
  -- Now apply to the sum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro lam _
  exact h lam

/-- First Bianchi identity holds for lowered tensor.
    R_{ρσμν} + R_{ρμνσ} + R_{ρνσμ} = 0

    This follows from first_bianchi by linearity of metric contraction. -/
theorem first_bianchi_lower (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannLower g ρ σ μ ν p + riemannLower g ρ μ ν σ p + riemannLower g ρ ν σ μ p = 0 := by
  unfold riemannLower
  -- Goal: Σ_λ g_{ρλ}(R^λ_{σμν} + R^λ_{μνσ} + R^λ_{νσμ}) = 0
  -- Factor out the metric and use first_bianchi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have h : ∀ lam : Fin 4,
      (g p) ρ lam * riemannTensor g lam σ μ ν p +
      (g p) ρ lam * riemannTensor g lam μ ν σ p +
      (g p) ρ lam * riemannTensor g lam ν σ μ p = 0 := by
    intro lam
    rw [← mul_add, ← mul_add]
    rw [first_bianchi g hSym lam σ μ ν p]
    ring
  apply Finset.sum_eq_zero
  intro lam _
  exact h lam

/-! ## Pair Swap Symmetry (From Axiom M3b) -/

/-- Helper lemma: riemannTensor expands to axiom-compatible form.
    This bridges our definition to the axiom formulation. -/
lemma riemannTensor_expand (g : DiscreteMetric) (lam σ μ ν : Fin 4) (p : LatticePoint) :
    riemannTensor g lam σ μ ν p =
    symmetricDiff (fun q => christoffelSymbol g lam ν σ q) μ p -
    symmetricDiff (fun q => christoffelSymbol g lam μ σ q) ν p +
    ∑ alpha : Fin 4, (christoffelSymbol g lam μ alpha p * christoffelSymbol g alpha ν σ p -
                      christoffelSymbol g lam ν alpha p * christoffelSymbol g alpha μ σ p) := by
  unfold riemannTensor christoffelDerivative
  -- Goal: A - B + ΣC - ΣD = A - B + Σ(C - D)
  -- Use algebraic manipulation
  have h : ∑ x : Fin 4, christoffelSymbol g lam μ x p * christoffelSymbol g x ν σ p -
           ∑ x : Fin 4, christoffelSymbol g lam ν x p * christoffelSymbol g x μ σ p =
           ∑ alpha : Fin 4, (christoffelSymbol g lam μ alpha p * christoffelSymbol g alpha ν σ p -
                             christoffelSymbol g lam ν alpha p * christoffelSymbol g alpha μ σ p) := by
    rw [← Finset.sum_sub_distrib]
  linarith [h]

/-- R_{ρσμν} = R_{μνρσ} (pair swap symmetry)

    This is AXIOM M3b from Axioms.Spacetime.
    The pair swap symmetry is a physical requirement from the Fourth Law
    (uniform reshaping symmetry / isotropy).

    In continuous GR, this follows from ∂_μ∂_ν = ∂_ν∂_μ (smooth second derivatives).
    On the discrete lattice, it must be postulated as a physical axiom.

    See Axioms/Spacetime.lean for full physical justification. -/
theorem riemann_lower_pair_swap (g : DiscreteMetric) (_hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (_hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannLower g ρ σ μ ν p = riemannLower g μ ν ρ σ p := by
  -- Expand riemannLower using riemannTensor_expand
  unfold riemannLower
  -- Rewrite each riemannTensor using the expanded form
  simp only [riemannTensor_expand]
  -- Now both sides match the axiom riemann_pair_swap exactly
  exact riemann_pair_swap g p ρ σ μ ν

/-! ## Antisymmetry in First Two Indices (Lowered) -/

/-- The fully covariant Riemann tensor has additional symmetries.
    R_{ρσμν} = -R_{σρμν} (antisymmetric in first two indices)

    PROOF: This follows from pair_swap + antisym34:
    R_{ρσμν} = R_{μνρσ}           (pair swap)
             = -R_{μνσρ}          (antisym34)
             = -R_{σρμν}          (pair swap) -/
theorem riemann_lower_antisym_12 (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannLower g ρ σ μ ν p = -riemannLower g σ ρ μ ν p := by
  -- Use pair swap and antisym34
  have hPairSwap := riemann_lower_pair_swap g hSym hNd
  calc riemannLower g ρ σ μ ν p
      = riemannLower g μ ν ρ σ p := hPairSwap ρ σ μ ν p
    _ = -riemannLower g μ ν σ ρ p := riemann_lower_antisym_34 g hSym μ ν ρ σ p
    _ = -riemannLower g σ ρ μ ν p := by rw [hPairSwap σ ρ μ ν p]

end DiscreteSpacetime.Geometry.Curvature
